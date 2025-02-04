from typing import List
import logging

from ailment import Block, Const
from ailment.expression import Convert, Register
import claripy
from angr.knowledge_plugins.key_definitions.constants import OP_BEFORE
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ....knowledge_plugins.key_definitions.atoms import MemoryLocation
from typing import Dict, Type, Callable
from ..utils import remove_labels
from .duplication_reverter import add_labels

import networkx as nx
import itertools
from ailment.block_walker import AILBlockWalkerBase
from ailment.statement import Call, Statement, ConditionalJump, Assignment, Store, Return

from ... import AnalysesHub

l = logging.getLogger(__name__)


class PairAILBlockWalker:
    def __init__(self, graph: nx.DiGraph, stmt_pair_handlers=None):
        self.graph = graph

        _default_stmt_handlers = {
            Assignment: self._handle_Assignment_pair,
            Call: self._handle_Call_pair,
            Store: self._handle_Store_pair,
            ConditionalJump: self._handle_ConditionalJump_pair,
            Return: self._handle_Return_pair,
        }

        self.stmt_pair_handlers: Dict[Type, Callable] = (
            stmt_pair_handlers if stmt_pair_handlers else _default_stmt_handlers
        )

    def _walk_block(self, block):
        walked_objs = {Assignment: set(), Call: set(), Store: set(), ConditionalJump: set(), Return: set()}

        # create a walker that will:
        # 1. recursively expand a stmt with the default handler then,
        # 2. record the stmt parts in the walked_objs dict with the overwritten handler
        #
        # CallExpressions are a special case that require a handler in expressions, since they are statements.
        walker = AILBlockWalkerBase()
        _default_stmt_handlers = {
            Assignment: walker._handle_Assignment,
            Call: walker._handle_Call,
            Store: walker._handle_Store,
            ConditionalJump: walker._handle_ConditionalJump,
            Return: walker._handle_Return,
        }

        def _handle_ail_obj(stmt_idx, stmt, block_):
            _default_stmt_handlers[type(stmt)](stmt_idx, stmt, block_)
            walked_objs[type(stmt)].add(stmt)

        def _handle_call_expr(expr_idx: int, expr: Call, stmt_idx: int, stmt: Statement, block_):
            walked_objs[Call].add(expr)

        _stmt_handlers = {typ: _handle_ail_obj for typ in walked_objs}
        walker.stmt_handlers = _stmt_handlers
        walker.expr_handlers[Call] = _handle_call_expr

        walker.walk(block)
        return walked_objs

    def walk(self):
        for b0, b1 in itertools.combinations(self.graph.nodes, 2):
            walked_obj_by_blk = {}

            for blk in (b0, b1):
                walked_obj_by_blk[blk] = self._walk_block(blk)

            for typ, objs0 in walked_obj_by_blk[b0].items():
                try:
                    handler = self.stmt_pair_handlers[typ]
                except KeyError:
                    continue

                if not objs0:
                    continue

                objs1 = walked_obj_by_blk[b1][typ]
                if not objs1:
                    continue

                for o0 in objs0:
                    for o1 in objs1:
                        handler(o0, b0, o1, b1)

    #
    # default handlers
    #

    def _handle_Assignment_pair(self, obj0, blk0, obj1, blk1):
        pass

    def _handle_Call_pair(self, obj0, blk0, obj1, blk1):
        pass

    def _handle_Store_pair(self, obj0, blk0, obj1, blk1):
        pass

    def _handle_ConditionalJump_pair(self, obj0, blk0, obj1, blk1):
        pass

    def _handle_Return_pair(self, obj0, blk0, obj1, blk1):
        pass


class ConstPropOptReverter(OptimizationPass):
    """
    Reverts the effects of constant propagation done by the compiler by converting two
    statements with a difference of a const and a symbolic variable and converting the constant
    into a symbolic variable, given that they have the same value on branches.
    """

    ARCHES = None
    PLATFORMS = None
    STAGE = OptimizationPassStage.DURING_REGION_IDENTIFICATION
    NAME = "Revert Constant Propagation Opt"
    DESCRIPTION = __doc__.strip()

    def __init__(self, func, region_identifier=None, reaching_definitions=None, **kwargs):
        self.ri = region_identifier
        self.rd = reaching_definitions
        super().__init__(func, **kwargs)

        self.write_graph = None
        self.resolution = False
        self.analyze()

    def _check(self):
        return True, {}

    def _analyze(self, cache=None):
        self.resolution = False
        self.out_graph = remove_labels(self._graph)
        # self.out_graph = self._graph

        _pair_stmt_handlers = {
            Call: self._handle_Call_pair,
            Return: self._handle_Return_pair,
        }

        if self.out_graph is None:
            return

        walker = PairAILBlockWalker(self.out_graph, stmt_pair_handlers=_pair_stmt_handlers)
        walker.walk()

        if not self.resolution:
            self.out_graph = None
        else:
            self.out_graph = add_labels(self.out_graph)

    #
    # Handle Similar Returns
    #

    def _handle_Return_pair(self, obj0: Return, blk0: Return, obj1, blk1):
        if obj0 is obj1:
            return

        rexp0, rexp1 = obj0.ret_exprs, obj1.ret_exprs
        if rexp0 is None or rexp1 is None or len(rexp0) != len(rexp1):
            return

        conflicts = {
            i: ret_exprs
            for i, ret_exprs in enumerate(zip(rexp0, rexp1))
            if hasattr(ret_exprs[0], "likes") and not ret_exprs[0].likes(ret_exprs[1])
        }
        # only single expr return is supported
        if len(conflicts) != 1:
            return

        _, ret_exprs = list(conflicts.items())[0]
        expr_to_blk = {ret_exprs[0]: blk0, ret_exprs[1]: blk1}
        # find the expression that is symbolic
        symb_expr, const_expr = None, None
        for expr in ret_exprs:
            unpacked_expr = expr
            if isinstance(expr, Convert):
                unpacked_expr = expr.operands[0]

            if isinstance(unpacked_expr, Const):
                const_expr = expr
            elif isinstance(unpacked_expr, Call):
                const_expr = expr
            else:
                symb_expr = expr

        if symb_expr is None or const_expr is None:
            return

        # now we do specific cases for matching
        if (
            isinstance(symb_expr, Register)
            and isinstance(const_expr, Call)
            and isinstance(const_expr.ret_expr, Register)
        ):
            """
            B0:
            return foo();   // considered constant)
            B1:
            return rax;     // considered symbolic

            =>

            B0:
            rax = foo();
            return rax;
            B1:
            return rax;
            """
            call_return_reg = const_expr.ret_expr
            if symb_expr.likes(call_return_reg):
                symb_return_stmt = expr_to_blk[symb_expr].statements[-1]
                const_block = expr_to_blk[const_expr]

                # rax = foo();
                reg_assign = Assignment(None, symb_expr, const_expr)

                # construct new constant block
                new_const_block = const_block.copy()
                new_const_block.statements = new_const_block.statements[:-1] + [reg_assign] + [symb_return_stmt.copy()]
                self._update_block(const_block, new_const_block)
                self.resolution = True
        else:
            l.debug("This case is not supported yet for Return depropagation")

    #
    # Handle Similar Calls
    #

    def _handle_Call_pair(self, obj0: Call, blk0, obj1: Call, blk1):
        if obj0 is obj1:
            return

        # verify both calls are calls to the same function
        if (isinstance(obj0.target, str) or isinstance(obj1.target, str)) and obj0.target != obj1.target:
            return
        elif not obj0.target.likes(obj1.target):
            return

        call0, call1 = obj0, obj1
        arg_conflicts = self.find_conflicting_call_args(call0, call1)
        # if there is no conflict, then there is nothing to fix
        if not arg_conflicts:
            return

        l.info(
            f"Found two calls at ({hex(blk0.addr)}, {hex(blk1.addr)}) that are similar. "
            f"Attempting to resolve const args now..."
        )

        # destroy old ReachDefs, since we need a new one
        self.rd = None
        observation_points = ("node", blk0.addr, OP_BEFORE), ("node", blk1.addr, OP_BEFORE)

        # attempt to do constant resolution for each argument that differs
        for i, args in arg_conflicts.items():
            a0, a1 = args[:]
            calls = {a0: call0, a1: call1}
            blks = {call0: blk0, call1: blk1}

            # we can only resolve two arguments where one is constant and one is symbolic
            const_arg = None
            sym_arg = None
            for arg in calls:
                if isinstance(arg, Const) and const_arg is None:
                    const_arg = arg
                elif not isinstance(arg, Const) and sym_arg is None:
                    sym_arg = arg

            if const_arg is None or sym_arg is None:
                continue

            if self.rd is None:
                self.rd = self.project.analyses.ReachingDefinitions(
                    subject=self._func, observation_points=observation_points
                )
            unwrapped_sym_arg = sym_arg.operands[0] if isinstance(sym_arg, Convert) else sym_arg
            try:
                # TODO: make this support more than just Loads
                # target must be a Load of a memory location
                target_atom = MemoryLocation(unwrapped_sym_arg.addr.value, unwrapped_sym_arg.size, "Iend_LE")
                const_state = self.rd.get_reaching_definitions_by_node(blks[calls[const_arg]].addr, OP_BEFORE)

                state_load_vals = const_state.get_value_from_atom(target_atom)
            except Exception:
                continue

            if not state_load_vals:
                continue

            state_vals = list(state_load_vals.values())
            # the symbolic variable MUST resolve to only a single value
            if len(state_vals) != 1:
                continue

            state_val = list(state_vals[0])[0]
            if hasattr(state_val, "concrete") and state_val.concrete:
                const_value = claripy.Solver().eval(state_val, 1)[0]
            else:
                continue

            if not const_value == const_arg.value:
                continue

            l.info(f"Constant argument at position {i} was resolved to symbolic arg {sym_arg}")
            const_call = calls[const_arg]
            const_arg_i = const_call.args.index(const_arg)
            const_call.args[const_arg_i] = sym_arg
            self.resolution = True

    @staticmethod
    def find_conflicting_call_args(call0: Call, call1: Call):
        if not call0.args or not call1.args:
            return None

        # TODO: update this to work for variable-arg functions
        if len(call0.args) != len(call1.args):
            return None

        # zip args of call 0 and 1 conflict if they are not like each other
        conflicts = {i: args for i, args in enumerate(zip(call0.args, call1.args)) if not args[0].likes(args[1])}

        return conflicts

    #
    # other handlers
    #

    def _handle_Assignment_pair(self, obj0, blk0, obj1, blk1):
        pass

    def _handle_Store_pair(self, obj0, blk0, obj1, blk1):
        pass

    def _handle_ConditionalJump_pair(self, obj0, blk0, obj1, blk1):
        pass

    #
    # utils
    #

    def in_stmts(self, call, blk):
        for stmt in blk.statements:
            if call == stmt:
                return True

            if isinstance(stmt, Store) and stmt.data == call:
                return True

        return False

    def _share_subregion(self, blocks: List[Block]) -> bool:
        for region in self.ri.regions_by_block_addrs:
            if all(block.addr in region for block in blocks):
                break
        else:
            return False

        return True


AnalysesHub.register_default("CallArgSimplifier", ConstPropOptReverter)
