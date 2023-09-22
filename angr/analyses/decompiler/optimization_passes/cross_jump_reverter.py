from collections import defaultdict
from typing import Any, Tuple, Dict, List, Optional
from itertools import count
import copy
import logging
import inspect

import networkx
import networkx as nx

import ailment
from ailment import AILBlockWalkerBase
from ailment.statement import Jump, ConditionalJump
from ailment.expression import Const
from .. import RegionIdentifier
from ..utils import to_ail_supergraph, remove_labels
from .duplication_reverter import add_labels

from ..condition_processor import ConditionProcessor, EmptyBlockNotice
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ..goto_manager import GotoManager
from ..structuring import RecursiveStructurer, PhoenixStructurer
from ..utils import to_ail_supergraph

l = logging.getLogger(__name__)


class AILCallCounter(AILBlockWalkerBase):
    """
    Helper class to count AIL Calls in a block
    """

    calls = 0

    def _handle_Call(self, stmt_idx: int, stmt: "Call", block: Optional["Block"]):
        self.calls += 1
        super()._handle_Call(stmt_idx, stmt, block)


def _number_of_calls_in(graph: networkx.DiGraph) -> int:
        counter = AILCallCounter()
        for node in graph.nodes:
            counter.walk(node)

        return counter.calls

class CrossJumpReverter(OptimizationPass):
    """
    Copies bad blocks
    """

    ARCHES = None
    PLATFORMS = None
    STAGE = OptimizationPassStage.DURING_REGION_IDENTIFICATION
    NAME = "Duplicate blocks destroyed with gotos"
    DESCRIPTION = "DUPLICATE"

    def __init__(
        self,
        func,
        node_idx_start=0,
        # settings
        max_level=10,
        call_dup_max=2,
        **kwargs,
    ):
        super().__init__(func, **kwargs)

        self.max_level = max_level
        self.node_idx = count(start=node_idx_start)
        self.call_dup_max = call_dup_max

        self.goto_manager: Optional[GotoManager] = None
        self.initial_gotos = None

        self.func_name = self._func.name
        self.binary_name = self.project.loader.main_object.binary_basename
        self.target_name = f"{self.binary_name}.{self.func_name}"
        self.graph_copy = None
        self.analyze()

    def _check(self):
        return True, None

    def _analyze(self, cache=None):
        # for each block with no successors and more than 1 predecessors, make copies of this block and link it back to
        # the sources of incoming edges
        self.graph_copy = to_ail_supergraph(remove_labels(networkx.DiGraph(self._graph)))
        #self.graph_copy = to_ail_supergraph(networkx.DiGraph(self._graph))
        self.last_graph = None
        graph_updated = False

        # attempt at most N levels
        for _ in range(self.max_level):
            success, graph_has_gotos = self._structure_graph()
            if not success:
                self.graph_copy = self.last_graph
                break

            if not graph_has_gotos:
                l.debug("Graph has no gotos. Leaving analysis...")
                break

            # make a clone of graph copy to recover in the event of failure
            self.last_graph = self.graph_copy.copy()
            r = self._analyze_core(self.graph_copy)
            if not r:
                break
            graph_updated = True

        # the output graph
        if graph_updated and self.graph_copy is not None:
            if self.goto_manager is not None and not (len(self.initial_gotos) < len(self.goto_manager.gotos)):
                #self.out_graph = self.graph_copy
                #self.out_graph = add_labels(remove_labels(self.graph_copy))
                self.out_graph = add_labels(self.graph_copy)


    #
    # taken from deduplicator
    #

    def _structure_graph(self):
        # reset gotos
        self.goto_manager = None

        # do structuring
        self.graph_copy = add_labels(self.graph_copy)
        self._ri = self.project.analyses[RegionIdentifier].prep(kb=self.kb)(
            self._func, graph=self.graph_copy, cond_proc=self._ri.cond_proc, force_loop_single_exit=False,
            complete_successors=True
        )
        rs = self.project.analyses[RecursiveStructurer].prep(kb=self.kb)(
            copy.deepcopy(self._ri.region),
            cond_proc=self._ri.cond_proc,
            func=self._func,
            structurer_cls=PhoenixStructurer
        )
        self.graph_copy = remove_labels(self.graph_copy)
        if not rs.result.nodes:
            l.critical(f"Failed to redo structuring on {self.target_name}")
            return False, False

        rs = self.project.analyses.RegionSimplifier(self._func, rs.result, kb=self.kb, variable_kb=self._variable_kb)
        self.goto_manager = rs.goto_manager
        if self.initial_gotos is None:
            self.initial_gotos = self.goto_manager.gotos

        return True, len(self.goto_manager.gotos) != 0 if self.goto_manager else False

    def _analyze_core(self, graph: networkx.DiGraph):
        # collect all nodes that have a goto
        to_update = {}
        for node in graph.nodes:
            gotos = self.goto_manager.gotos_in_block(node)
            # TODO: support if-stmts
            if not gotos or len(gotos) >= 2:
                continue

            # only single reaching gotos
            goto = list(gotos)[0]
            for goto_target in graph.successors(node):
                if goto_target.addr == goto.dst_addr:
                    break
            else:
                goto_target = None

            if goto_target is None:
                continue

            if graph.out_degree(goto_target) != 1:
                continue

            counter = AILCallCounter()
            counter.walk(goto_target)
            if counter.calls > self.call_dup_max:
                continue

            # og_block -> suc_block (goto target)
            to_update[node] = goto_target

        if not to_update:
            return False

        for target_node, goto_node in to_update.items():
            # always make a copy if there is a goto edge
            cp = copy.deepcopy(goto_node)
            cp.idx = next(self.node_idx)

            # remove this goto edge from original
            graph.remove_edge(target_node, goto_node)

            # add a new edge to the copy
            graph.add_edge(target_node, cp)

            # make sure the copy has the same successor as before!
            suc = list(graph.successors(goto_node))[0]
            graph.add_edge(cp, suc)

            # kill the original if we made enough copies to drain in-degree
            if graph.in_degree(goto_node) == 0:
                graph.remove_node(goto_node)

        # TODO: add single chain later:
        # i.e., we need to copy the entire chain of single successor nodes in
        # this goto chain.
        return True
