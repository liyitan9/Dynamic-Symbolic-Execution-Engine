# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import sys

import io 
import z3

from . import ast, int
# new import
from functools import reduce
from copy import deepcopy

class SymState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concerete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        st = int.State()
        for (k, v) in self.env.items():
            st.env[k] = model.eval(v)
        return st

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState()
        child.env = dict(self.env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()


class SymExec(ast.AstVisitor):
    def __init__(self):
        self.states = []

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
        self.states = [state]
        return self.visit(ast, state = self.states)

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs

        assert False       

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            return z3.Not(kids[0])
        if node.op == "and":
            return z3.And(kids)
        elif node.op == "or":
            return z3.Or(kids)
        
        assert False
        
    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None

        if node.op == "+":
            fn = lambda x, y: x + y

        elif node.op == "-":
            fn = lambda x, y: x - y

        elif node.op == "*":
            fn = lambda x, y: x * y

        elif node.op == "/":
            fn = lambda x, y: x / y

        assert fn is not None
        return reduce(fn, kids)

    def visit_SkipStmt(self, node, *args, **kwargs):
        return kwargs["state"]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        for st in kwargs['state']:
            print(st)
            print(st.pick_concerete())
        return kwargs["state"]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        for st in kwargs["state"]:
            st.env[node.lhs.name] = self.visit(node.rhs, *args, state = st)
        return kwargs["state"]

    def visit_IfStmt(self, node, *args, **kwargs):
        then_states = []
        else_states = []
        for st in kwargs["state"]:
            cond = self.visit(node.cond, state = st)
            then_st, else_st = st.fork()
            then_st.add_pc(cond)
            else_st.add_pc(z3.Not(cond))
            if then_st.is_empty():
                then_st.mk_error()
            else:
                then_states.append(then_st)
            if else_st.is_empty():
                else_st.mk_error()
            else:
                else_states.append(else_st)
        if then_states:
            self.visit(node.then_stmt, state=then_states)

        if node.has_else() and else_states:
            self.visit(node.else_stmt, state=else_states)

        kwargs["state"][:] = then_states + else_states

        return kwargs["state"]           

    def visit_WhileStmt(self, node, *args, **kwargs):
        loop_states = []
        exit_states = []
        count = kwargs.get('count', 1)
        for st in kwargs["state"]:
            cond = self.visit(node.cond, state = st)
            lp_st, et_st = st.fork()
            if count <= 10:
                lp_st.add_pc(cond)
                if lp_st.is_empty():
                    lp_st.mk_error()
                else:
                    loop_states.append(lp_st)
            et_st.add_pc(z3.Not(cond))
            if et_st.is_empty():
                et_st.mk_error()
            else:
                exit_states.append(et_st)
        
        if count <= 10 and loop_states:
            self.visit(node.body, state=loop_states)
            self.visit(node, state=loop_states, count=count+1)
        kwargs["state"][:] = loop_states + exit_states
        return kwargs["state"]



    def visit_AssertStmt(self, node, *args, **kwargs):
        # Don't forget to print an error message if an assertion might be violated
        new_states = []

        for st in kwargs["state"]:
            cond = self.visit(node.cond, state = st)
            st_true, st_false = st.fork()
            st_true.add_pc(cond)
            st_false.add_pc(z3.Not(cond))
            
            if not st_false.is_empty():
                st_false.mk_error()
                print("Error: Assertion might be violated")
                print(st_false.pick_concerete())
            if st_true.is_empty():
                st_true.mk_error()
                print("Error: Assertion will definitely be violated")
            elif not st_true.is_empty():
                new_states.append(st_true)

        kwargs["state"][:] = new_states
        return kwargs["state"]
            

    def visit_AssumeStmt(self, node, *args, **kwargs):
            new_states = []
            for st in kwargs["state"]:
                st.add_pc(self.visit(node.cond, *args, state=st))
                if st.is_empty():
                    st.mk_error()
                else:
                    new_states.append(st)

            kwargs["state"][:] = new_states        
            return kwargs["state"]

    def visit_HavocStmt(self, node, *args, **kwargs):
        for st in kwargs["state"]:
            for v in node.vars:
                st.env[v.name] = z3.FreshInt(v.name)
        return kwargs["state"]

    def visit_StmtList(self, node, *args, **kwargs):
        st = kwargs["state"]
        nkwargs = dict(kwargs)
        for stmt in node.stmts:
            nkwargs["state"] = st
            st = self.visit(stmt, *args, state = st)
        return st


def _parse_args():
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = SymState()
    sym = SymExec()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic state reached')
            print(out)
        print('[symexec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
