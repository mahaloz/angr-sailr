import itertools
from typing import Any, Tuple, Dict, List, TYPE_CHECKING, Optional, Set, Union
from itertools import count
import copy
import logging
import inspect

import networkx
import networkx as nx

import ailment
from ailment import Block
from ailment.statement import Jump, ConditionalJump, Return, Label
from ailment.expression import Const
from ailment.block_walker import AILBlockWalkerBase

from ..condition_processor import ConditionProcessor, EmptyBlockNotice
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ..graph_region import GraphRegion
from ..structuring import RecursiveStructurer, PhoenixStructurer
from ..goto_manager import GotoManager, Goto
from .. import RegionIdentifier
from ..region_walker import RegionWalker
from ..structuring.structurer_nodes import MultiNode
from ..utils import remove_labels, to_ail_supergraph, add_labels

if TYPE_CHECKING:
    from ailment import Block
    from ailment.statement import Call


_l = logging.getLogger(name=__name__)


class RegionNodeUnpacker(RegionWalker):
    nodes = []
    def walk_node(self, region, node):
        if isinstance(node, MultiNode):
            for _node in node.nodes:
                self.walk_node(region, _node)
        else:
            self.nodes.append(node)


class GotoEndnodeRegionFinder(RegionWalker):
    def __init__(self, goto_manager: GotoManager, endnode_heads: Set[Block]):
        super().__init__()
        self._goto_manager = goto_manager
        self._endnode_heads = endnode_heads
        # (region, endnode_head, overlapping_blocks)
        # listed in order of DFS regions traversed
        self.goto_regions = list()
        self._debug = True

    def walk_node(self, region, node):
        if not region.graph:
            return

        region_graph = region.graph_with_successors if region.graph_with_successors else region.graph
        for region_node in region_graph.nodes:
            # every return region needs to have more than 1 edge for a real goto to exist
            node_is_graph = isinstance(region_node, GraphRegion)
            if ((region_node in self._endnode_heads) or (node_is_graph and region_node.head in self._endnode_heads)) \
                    and region_graph.in_degree(region_node) > 1:
                return_preds = sorted(list(region_graph.predecessors(region_node)), key=lambda x: x.addr)
                return_preds = sorted(return_preds, key=lambda x: isinstance(x, (Block, MultiNode)), reverse=True)
                for pred in return_preds:
                    region_node_head = region_node.head if node_is_graph else region_node
                    if self.region_contains_goto(pred, region_node_head):
                        other_preds = filter(lambda x: x is not pred, return_preds)
                        overlapping_blocks = set(itertools.chain.from_iterable(
                            [EagerReturnsSimplifier.unpack_region_nodes(other_pred) for other_pred in other_preds]
                        ))
                        # XXX: this is a hack to remove single-block regions from the overlapping blocks
                        if pred in overlapping_blocks:
                            overlapping_blocks.remove(pred)

                        self.goto_regions.append((pred, region_node_head, overlapping_blocks))
                        break

    def region_contains_goto(self, region: Union[GraphRegion, Block], dst_head: Block) -> bool:
        if isinstance(region, Block):
            if self._goto_manager.is_goto_edge(region, dst_head):
                return True
        elif isinstance(region, MultiNode):
            for node in region.nodes:
                goto = self.region_contains_goto(node, dst_head)
                if goto is not None:
                    return True
        elif isinstance(region, GraphRegion):
            graph = region.graph_with_successors if region.graph_with_successors else region.graph
            for node in graph.nodes:
                goto = self.region_contains_goto(node, dst_head)
                if goto is not None:
                    return True

        return False


class AILCallCounter(AILBlockWalkerBase):
    """
    Helper class to count AIL Calls in a block
    """

    calls = 0

    def _handle_Call(self, stmt_idx: int, stmt: "Call", block: Optional["Block"]):
        self.calls += 1
        super()._handle_Call(stmt_idx, stmt, block)


class EagerReturnsSimplifier(OptimizationPass):
    """
    Some compilers (if not all) generate only one returning block for a function regardless of how many returns there
    are in the source code. This oftentimes result in irreducible graphs and reduce the readability of the decompiled
    code. This optimization pass will make the function return eagerly by duplicating the return site of a function
    multiple times and assigning one copy of the return site to each of its sources when certain thresholds are met.

    Note that this simplifier may reduce the readability of the generated code in certain cases, especially if the graph
    is already reducible without applying this simplifier.

    :ivar int max_level:    Number of times that we repeat the process of making returns eager.
    :ivar int min_indegree: The minimum in-degree of the return site to be duplicated.
    :ivar node_idx:         The next node index. Each duplicated return site gets assigned a unique index, otherwise
                            those duplicates will be considered as the same block in the graph because they have the
                            same hash.
    """

    ARCHES = None
    PLATFORMS = None
    STAGE = OptimizationPassStage.DURING_REGION_IDENTIFICATION
    NAME = "Duplicate return blocks to reduce goto statements"
    DESCRIPTION = inspect.cleandoc(__doc__[: __doc__.index(":ivar")])  # pylint:disable=unsubscriptable-object

    def __init__(
        self,
        func,
        # internal parameters that should be used by Clinic
        node_idx_start=0,
        # settings
        max_duplication_rounds=10,
        min_indegree=2,
        max_round_call_duplications=2,
        max_level_goto_check=2,
        **kwargs,
    ):
        super().__init__(func, **kwargs)

        self.node_idx = count(start=node_idx_start)

        self.max_duplication_rounds = max_duplication_rounds
        self.min_indegree = min_indegree
        self.max_round_call_duplication = max_round_call_duplications
        self.max_level_goto_check = max_level_goto_check

        self.goto_manager: Optional[GotoManager] = None
        self.func_name = self._func.name
        self.binary_name = self.project.loader.main_object.binary_basename
        self.target_name = f"{self.binary_name}.{self.func_name}"
        self._write_graph = None
        self.analyze()

    def _check(self):
        # does this function have end points?
        if not self._func.endpoints:
            return False, None

        return True, None

    def _analyze(self, cache=None):
        # for each block with no successors and more than 1 predecessors, make copies of this block and link it back to
        # the sources of incoming edges
        self._write_graph = networkx.DiGraph(self._graph)
        self.last_graph = None
        graph_updated = False

        for rnd in range(self.max_duplication_rounds):
            success, graph_has_gotos = self._structure_graph()
            if not success:
                _l.info("Failed to structure this graph. Recovering with last graph...")
                self._write_graph = self.last_graph
                break

            if not graph_has_gotos:
                _l.info("Graph has no gotos. Leaving analysis...")
                break

            # make a clone of graph copy to recover in the event of failure
            self.last_graph = self._write_graph.copy()
            r = self._analyze_core(self._write_graph)
            if not r:
                break
            graph_updated = True

        # the output graph
        if graph_updated and self._write_graph is not None:
            success, graph_has_gotos = self._structure_graph()
            if not success:
                self._write_graph = self.last_graph

            if self._write_graph is not None:
                self.out_graph = add_labels(remove_labels(self._write_graph))


    #
    # taken from deduplicator
    #

    def _structure_graph(self):
        # reset gotos
        self.goto_manager = None

        # do structuring
        self._ri = self.project.analyses[RegionIdentifier].prep(kb=self.kb)(
            self._func, graph=self._write_graph, cond_proc=self._ri.cond_proc, force_loop_single_exit=False,
            complete_successors=True
        )
        rs = self.project.analyses[RecursiveStructurer].prep(kb=self.kb)(
            copy.deepcopy(self._ri.region),
            cond_proc=self._ri.cond_proc,
            func=self._func,
            structurer_cls=PhoenixStructurer
        )
        if not rs.result.nodes:
            _l.critical(f"Failed to redo structuring on {self.target_name}")
            return False, False

        rs = self.project.analyses.RegionSimplifier(self._func, rs.result, kb=self.kb, variable_kb=self._variable_kb)
        self.goto_manager = rs.goto_manager
        if self.goto_manager is None:
            _l.critical(f"Failed to region simplification on {self.target_name}")
            return False, False

        return True, len(self.goto_manager.gotos) != 0

    def _find_endnode_regions(self, graph: networkx.DiGraph) \
            -> Dict[Any, Tuple[List[Tuple[Any, Any]], networkx.DiGraph]]:
        endnodes = [node for node in graph.nodes() if graph.out_degree[node] == 0]

        # to_update is keyed by the region head.
        # this is because different end nodes may lead to the same region head: consider the case of the typical "fork"
        # region where stack canary is checked in x86-64 binaries.
        endnode_regions: Dict[Any, Tuple[List[Tuple[Any, Any]], networkx.DiGraph]] = {}

        for end_node in endnodes:
            in_edges = list(graph.in_edges(end_node))

            if len(in_edges) > 1:
                region = networkx.DiGraph()
                region.add_node(end_node)
                region_head = end_node
            elif len(in_edges) == 1:
                # back-trace until it reaches a node with two predecessors
                region, region_head = self._single_entry_region(graph, end_node)
                tmp_in_edges = graph.in_edges(region_head)
                # remove in_edges that are coming from a node inside the region
                in_edges = []
                for src, dst in tmp_in_edges:
                    if src not in region:
                        in_edges.append((src, dst))
            else:  # len(in_edges) == 0
                continue

            # region and in_edge might have been updated. re-check
            if not in_edges:
                # this is a single connected component in the graph
                # no need to duplicate anything
                continue
            if len(in_edges) == 1:
                # there is no need to duplicate it
                continue
            if len(in_edges) < self.min_indegree:
                # does not meet the threshold
                continue

            if any(self._is_indirect_jump_ailblock(src) for src, _ in in_edges):
                continue

            # to assure we are not copying like crazy, set a max amount of code (which is estimated in calls)
            # that can be copied in a region
            if self._number_of_calls_in(region) > self.max_round_call_duplication:
                continue

            endnode_regions[region_head] = in_edges, region

        return endnode_regions

    def _copy_region(self, pred_nodes: List[Block], region_head: Block, region, graph):
        _l.debug(f"-> copying {pred_nodes} -> {repr(region_head)}")
        copies = {}
        queue = [(pred, region_head) for pred in pred_nodes]
        while queue:
            pred, node = queue.pop(0)
            if node in copies:
                node_copy = copies[node]
            else:
                node_copy = copy.deepcopy(node)
                node_copy.idx = next(self.node_idx)
                copies[node] = node_copy

            # modify Jump.target_idx accordingly
            _l.debug(f"----> adding edge {repr(pred)} -> {repr(node_copy)}")
            graph.add_edge(pred, node_copy)
            try:
                last_stmt = ConditionProcessor.get_last_statement(pred)
                if isinstance(last_stmt, Jump) and isinstance(last_stmt.target, Const):
                    if last_stmt.target.value == node_copy.addr:
                        last_stmt.target_idx = node_copy.idx
            except EmptyBlockNotice:
                pass

            for succ in region.successors(node):
                queue.append((node_copy, succ))

        # delete the old edge to the return node
        for pred_node in pred_nodes:
            graph.remove_edge(pred_node, region_head)
            _l.debug(f"----> deleting edge {repr(pred_node)} -> {repr(region_head)}")
        if region_head in graph and graph.in_degree(region_head) == 0:
            graph.remove_nodes_from(region)

    @staticmethod
    def find_goto_connected_regions(top_region, goto_manager, target_nodes):
        goto_finder = GotoEndnodeRegionFinder(goto_manager, target_nodes)
        goto_finder.walk(top_region)
        return goto_finder.goto_regions

    @staticmethod
    def unpack_region_nodes(region):
        if isinstance(region, Block):
            return [region]
        elif isinstance(region, MultiNode):
            return [node for node in region.nodes]
        else:
            unpacker = RegionNodeUnpacker()
            unpacker.walk(region)
            return unpacker.nodes

    def _analyze_core(self, graph: networkx.DiGraph):
        # algorithm overview:
        # 1. Find all the end regions in the graph
        # 2. Iterate down the region graphs, find a region graph with a goto in it pointing to a ret region
        # 3. Copy the end region

        # mapped: [region_head] -> (in_edges, region)
        endnode_regions = self._find_endnode_regions(graph)
        goto_connected_regions = self.find_goto_connected_regions(
            self._ri.region, self.goto_manager, sorted(list(set(endnode_regions.keys())), key=lambda x: x.addr)
        )
        # there are gotos, but none of those gotos go to an endnode region (a return)
        if not goto_connected_regions:
            return False

        goto_connected_region = goto_connected_regions[0]
        region_pred, endnode_region_head, overlapping_region_blocks = goto_connected_region
        return_pred_nodes = {
            node for node in self.unpack_region_nodes(region_pred)
            # exclude blocks that are in the overlapping regions to allow gotos to be unique for regions
            if node in graph and endnode_region_head in list(graph.successors(node)) and node not in overlapping_region_blocks
        }
        return_pred_nodes = sorted(list(return_pred_nodes), key=lambda x: x.addr)
        _l.debug(f"Fixing up: {region_pred} {repr(endnode_region_head)} {repr(endnode_regions[endnode_region_head][1])}")
        self._copy_region(return_pred_nodes, endnode_region_head, endnode_regions[endnode_region_head][1], graph)
        return True

    @staticmethod
    def _number_of_calls_in(graph: networkx.DiGraph) -> int:
        counter = AILCallCounter()
        for node in graph.nodes:
            counter.walk(node)

        return counter.calls

    @staticmethod
    def _single_entry_region(graph, end_node) -> Tuple[networkx.DiGraph, Any]:
        """
        Back track on the graph from `end_node` and find the longest chain of nodes where each node has only one
        predecessor and one successor (the second-to-last node may have two successors to account for the typical
        stack-canary-detection logic).

        :param end_node:    A node in the graph.
        :return:            A graph of nodes where the first node either has no predecessors or at least two
                            predecessors.
        """

        def _is_fork_node(node_) -> bool:
            """
            Check if the node and its successors form a "fork" region. A "fork" region is a region where:
            - The entry node has two successors,
            - Each successor has only the entry node as its predecessor.
            - Each successor has no successors.
            """

            succs = list(graph.successors(node_))
            if len(succs) != 2:
                return False
            for succ in succs:
                if graph.in_degree[succ] != 1:
                    return False
                if graph.out_degree[succ] != 0:
                    return False
            return True

        region = networkx.DiGraph()
        region.add_node(end_node)

        traversed = {end_node}
        region_head = end_node
        while True:
            preds = list(graph.predecessors(region_head))
            if len(preds) != 1:
                break
            second_to_last_node = region_head is end_node

            pred_node = preds[0]

            if pred_node in traversed:
                break

            if second_to_last_node:
                if _is_fork_node(pred_node):
                    # add the entire "fork" to the region
                    for succ in graph.successors(pred_node):
                        region.add_edge(pred_node, succ)
                elif graph.out_degree[pred_node] != 1:
                    # the predecessor has more than one successor, and it's not a fork node
                    break

                if graph.in_degree[pred_node] == 1:
                    # continue search
                    pass
                else:
                    region.add_edge(pred_node, region_head)
                    traversed.add(pred_node)
                    region_head = pred_node
                    break
            elif not second_to_last_node and graph.out_degree[pred_node] != 1:
                break

            region.add_edge(pred_node, region_head)
            traversed.add(pred_node)
            region_head = pred_node

        return region, region_head

    @staticmethod
    def _is_indirect_jump_ailblock(block: "Block") -> bool:
        if block.statements and isinstance(block.statements[-1], Jump):
            last_stmt = block.statements[-1]
            if not isinstance(last_stmt.target, Const):
                # it's an indirect jump (assuming the AIL block is properly optimized)
                return True
        return False

    @staticmethod
    def _is_single_return_stmt_region(region: networkx.DiGraph) -> bool:
        """
        Checks weather the provided region contains only one return statement. This stmt
        can be connected by many jumps, but none can be conditional. A valid case is:
        [Jmp] -> [Jmp] -> [Ret]
        """
        valid_stmt_types = (Return, Jump, Label)
        for node in region.nodes():
            if isinstance(node, Block):
                for stmt in node.statements:
                    if not isinstance(stmt, valid_stmt_types):
                        return False
        return True
