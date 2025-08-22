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
import random

class ConcolicState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        self.concrete = dict()
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

    def pick_concrete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        for (k, v) in self.env.items():
            self.concrete[k] = model.eval(v, model_completion=True).as_long()
        return z3.sat

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = ConcolicState()
        child.env = dict(self.env)
        child.concrete = dict(self.concrete)
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

        for k, v in self.concrete.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('\n')
        return buf.getvalue()


class ConExec(ast.AstVisitor):
    def __init__(self):
        self.states = []

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
        self.states = [state]
        return self.visit(ast, state = self.states)

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs["state"].env[node.name], kwargs["state"].concrete[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val), node.val

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val), node.val

    def visit_RelExp(self, node, *args, **kwargs):
        lhs_sym, lhs_con = self.visit(node.arg(0), *args, **kwargs)
        rhs_sym, rhs_con = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return lhs_sym <= rhs_sym, lhs_con <= rhs_con
        if node.op == "<":
            return lhs_sym < rhs_sym, lhs_con < rhs_con
        if node.op == "=":
            return lhs_sym == rhs_sym, lhs_con == rhs_con
        if node.op == ">=":
            return lhs_sym >= rhs_sym, lhs_con >= rhs_con
        if node.op == ">":
            return lhs_sym > rhs_sym, lhs_con > rhs_con

        assert False       

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        kids_sym = [kid[0] for kid in kids]
        kids_con = [kid[1] for kid in kids]
        
        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            return z3.Not(kids_sym[0]), not kids_con[0]
        
        fn = None
        base = None
        if node.op == "and":
            fn = lambda x, y: x and y
            base = True
            assert fn is not None
            return z3.And(kids_sym), reduce(fn, kids_con, base)
        elif node.op == "or":
            fn = lambda x, y: x or y
            base = False
            assert fn is not None
            return z3.Or(kids_sym), reduce(fn, kids_con, base)
        
        assert False
        
    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        kids_sym = [kid[0] for kid in kids]
        kids_con = [kid[1] for kid in kids]

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
        return reduce(fn, kids_sym), reduce(fn, kids_con)

    def visit_SkipStmt(self, node, *args, **kwargs):
        return kwargs["state"]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        for st in kwargs['state']:
            print(st)
        return kwargs["state"]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        for st in kwargs["state"]:
            st.env[node.lhs.name], st.concrete[node.lhs.name] = self.visit(node.rhs, *args, state = st)
        return kwargs["state"]

    def visit_IfStmt(self, node, *args, **kwargs):
        then_states = []
        else_states = []
        for st in kwargs["state"]:
            cond_sym, cond_con = self.visit(node.cond, state = st)
            then_st, else_st = st.fork()
            then_st.add_pc(cond_sym)
            else_st.add_pc(z3.Not(cond_sym))
            
            if(cond_con):
                then_states.append(then_st)

                if else_st.is_empty():
                    pass
                else:
                    else_st.pick_concrete()
                    else_states.append(else_st)
            else:
                else_states.append(else_st)

                if then_st.is_empty():
                    pass
                else:
                    then_st.pick_concrete()
                    then_states.append(then_st)

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
            cond_sym, cond_con = self.visit(node.cond, state=st)
            lp_st, et_st = st.fork()

            et_st.add_pc(z3.Not(cond_sym))
            if not et_st.is_empty():
                et_st.pick_concrete()
                exit_states.append(et_st)
            else:
                pass
            
            if count <= 10:
                lp_st.add_pc(cond_sym)
                if not lp_st.is_empty():
                    lp_st.pick_concrete()
                    loop_states.append(lp_st)
                else:
                    pass
                
        if count <= 10 and loop_states:
            self.visit(node.body, state=loop_states)
            self.visit(node, state=loop_states, count=count + 1)
        kwargs["state"][:] = loop_states + exit_states
        return kwargs["state"]


    def visit_AssertStmt(self, node, *args, **kwargs):
        new_states = []

        for st in kwargs["state"]:
            cond_sym, cond_con = self.visit(node.cond, state=st)
            ok_st, err_st = st.fork()
            ok_st.add_pc(cond_sym)                  
            err_st.add_pc(z3.Not(cond_sym))       
            err_st.mk_error()

            if not cond_con:
                if ok_st.pick_concrete() is None:
                    print("Warning: Unable to find a satisfying model for assertion pass branch. Possible violation definitly happen.")
                    new_states.append(err_st)
                else:
                    new_states.append(ok_st)
                    new_states.append(err_st)
                
            else:
                if not err_st.is_empty():
                    err_st.pick_concrete()
                    new_states.append(ok_st)
                    new_states.append(err_st)
                else:
                    new_states.append(ok_st)

        kwargs["state"][:] = new_states
        return kwargs["state"]


    def visit_AssumeStmt(self, node, *args, **kwargs):
        new_states = []

        for st in kwargs["state"]:
            cond_sym, cond_con = self.visit(node.cond, state=st)

            if cond_con:
                st.add_pc(cond_sym)
                new_states.append(st)
            else:
                st.add_pc(cond_sym)
                if st.pick_concrete() is None:
                    continue

                new_states.append(st)

        kwargs["state"][:] = new_states
        return kwargs["state"]
    

    def visit_HavocStmt(self, node, *args, **kwargs):
        for st in kwargs["state"]:
            for v in node.vars:
                st.env[v.name] = z3.FreshInt(v.name)
                if v.name not in st.concrete:
                    st.concrete[v.name] = 0
        return kwargs["state"]

        self.concrete = didict()
        
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
    st = ConcolicState()
    sym = ConExec()

    states = sym.run(prg, st)
    if states is None:
        print('[conexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[conexec]: symbolic state reached')
            print(out)
        print('[conexec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
