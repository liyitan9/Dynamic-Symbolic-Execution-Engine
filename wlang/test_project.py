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

import unittest

from . import ast, concolic_incremental
import z3
import os
from unittest.mock import patch
from io import StringIO

class TestSym (unittest.TestCase):

    def test_branch(self):
        program = """
        havoc x, y; 
        if x + y > 10 then {
            x := x + 1; 
            y := y - 1
        } else {
            y := y / 1;
            x := x * 10
        };
        x := x + 2;
        if (2 * x + 2 * y) > 20 then {
            x := x + 12;
            y := y / 2
        } else {
            x := x + 4;
            y := y + 2 * x
        }
        """
        ast_tree = ast.parse_string(program)
        engine = concolic_incremental.ConExec()
        initial_state = concolic_incremental.ConcolicState()
        final_states = [state for state in engine.run(ast_tree, initial_state)]
        # for s in final_states:
        #     print(s)
        self.assertEqual(len(final_states), 3)
        out_no_error = [s for s in final_states if not s.is_error()]
        self.assertEqual(len(out_no_error), 3)
        self.assertTrue(all(var in s.env for s in final_states for var in ['x', 'y']))

        
    def test_error_message(self):
        program = """
        havoc x;
        if x > 5 then
            skip
        else
            skip;
        assert x > 10
        """
        ast_tree = ast.parse_string(program)
        engine = concolic_incremental.ConExec()
        initial_state = concolic_incremental.ConcolicState()
        final_states = [state for state in engine.run(ast_tree, initial_state)]
        # for s in final_states:
        #     print(s)
        #     print(f"Is Error State? {s.is_error()}")
        self.assertEqual(len(final_states), 3)
        out_no_error = [s for s in final_states if not s.is_error()]
        self.assertEqual(len(out_no_error), 1)
        self.assertIn('x', final_states[0].env)
        self.assertIn('x', final_states[1].env)
        self.assertIn('x', final_states[2].env)


    def test_while(self):
        program = """
        havoc x, y, z, w;
        if not (w = 100) then x := x + 1 else x := x + 2;
        if not (y = 100) then x := x + 1 else x := x + 2;
        while x <= 10 and true do {
            if not (z >= 100 or false) then x := x + 1 else x := x + 2
        }
        """
        ast_tree = ast.parse_string(program)
        engine = concolic_incremental.ConExec()
        initial_state = concolic_incremental.ConcolicState()
        final_states = [state for state in engine.run(ast_tree, initial_state)]
        self.assertEqual(len(final_states), 84)
        out_no_error = [s for s in final_states if not s.is_error()]
        self.assertEqual(len(out_no_error), 84)
        self.assertTrue(all(var in s.env for s in final_states for var in ['x', 'y', 'z', 'w']))
        
    
    def test_double_havoc_1(self):
        prg1 = """
        havoc x, y;
        if (x > 0 and y < 0) then
            x := x + 1
        else
            y := y - 1;
        assume y > x;
        assert y > x + 100
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        # for s in out:
        #     print(s)
        #     print(f"Is Error State? {s.is_error()}")
        self.assertEqual(len(out), 2)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 1)
        self.assertTrue(all(var in s.env for s in out for var in ['x', 'y']))
    
    def test_double_havoc_2(self):
        program = """
        havoc x;
        assume x > 5;
        havoc x;
        assert x < 5;
        print_state  
        """
        ast_tree = ast.parse_string(program)
        engine = concolic_incremental.ConExec()
        initial_state = concolic_incremental.ConcolicState()
        final_states = [state for state in engine.run(ast_tree, initial_state)]
        # for s in final_states:
        #     print(s)
        #     print(f"Is Error State? {s.is_error()}")
        self.assertEqual(len(final_states), 2)
        out_no_error = [s for s in final_states if not s.is_error()]
        self.assertEqual(len(out_no_error), 1)
        self.assertTrue(all(var in s.env for s in final_states for var in ['x']))

    def test_if_no_else(self):
        program = """
        havoc x;
        if x > 5 then
            skip
        """
        ast_tree = ast.parse_string(program)
        engine = concolic_incremental.ConExec()
        initial_state = concolic_incremental.ConcolicState()
        final_states = [state for state in engine.run(ast_tree, initial_state)]
        self.assertEqual(len(final_states), 2)
        out_no_error = [s for s in final_states if not s.is_error()]
        self.assertEqual(len(out_no_error), 2)
        self.assertTrue(all(var in s.env for s in final_states for var in ['x']))

    def test_assert_pass(self):
        prg1 = """
        havoc x;
        assume x > 5;
        assert x > 0
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 1)
        self.assertTrue(all(var in s.env for s in out for var in ['x']))

    def test_assert_with_relExp(self):
        prg1 = """
        havoc a;
        b := 2;
        c := 3;
        assert not (a = b);
        assert true;
        assert not false;
        assert ((a < b) and (c < 20)) or (c = 3)
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        # for s in out:
        #     print(s)
        self.assertEqual(len(out), 2)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 1)
        self.assertTrue(all(var in s.env for s in out for var in ['a', 'b', 'c']))
        self.assertEqual(out[0].concrete['b'], 2)
        self.assertEqual(out[0].concrete['c'], 3)
        self.assertEqual(out[1].concrete['b'], 2)
        self.assertEqual(out[1].concrete['c'], 3)


    def test_assume_with_assert(self):
        prg1 = "a := 10; havoc x; assume a < 10 or x > 10; assert x > 15"

        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        # for s in out:
        #     print(s)
        self.assertEqual(len(out), 2)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 1)
        self.assertTrue(all(var in s.env for s in out for var in ['a', 'x']))
        self.assertEqual(out[0].concrete['a'], 10)
        self.assertEqual(out[1].concrete['a'], 10)

    def test_simple_if_branch(self):
        prg1 = """
        havoc x;       
        r := 0;
        if (x > 8) then
            r := x - 7;
        if (x < 5) then
            r := x - 2
        """

        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        # for s in out:
        #     print(s)
        self.assertEqual(len(out), 3)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 3)
        self.assertTrue(all(var in s.env for s in out for var in ['r', 'x']))

        
    def test_visit_relexp_assert(self):
        engine = concolic_incremental.ConExec()
        initial_state = concolic_incremental.ConcolicState()
        initial_state.env['x'] = z3.FreshInt("x")
        initial_state.env['y'] = z3.FreshInt("y")
        initial_state.pick_concrete()
        print(initial_state)
        invalid_rel_exp = ast.RelExp(ast.IntVar('x'), '!=', ast.IntVar('y'))
        with self.assertRaises(AssertionError):
            [s for s in engine.visit(invalid_rel_exp, state=initial_state)]

    def test_symstate(self):
        solver = z3.Solver()
        st = concolic_incremental.ConcolicState(solver)
        self.assertEqual(st._solver, solver)
        prg1 = """
        havoc x;
        assume x > 5
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)
        self.assertIsNotNone(repr(st))
        self.assertIsNotNone(st.to_smt2())
        st = concolic_incremental.ConcolicState()
        st.env['x'] = z3.FreshInt("x")
        st.add_pc(st.env['x'] > 5)
        st.add_pc(st.env['x'] < 5)
        self.assertIsNone(st.pick_concrete())
        st.mk_error()
        self.assertTrue(st.is_error())
            
    def test_visit_AExp_unknown(self):
        node = ast.AExp(op="+-", args=[ast.IntConst(1),ast.IntConst(2)])
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        with self.assertRaises(AssertionError):
            out = [s for s in engine.visit(node, state = st)]
            
    def test_visit_BExp_unknown(self):
        node = ast.BExp(op="no", args=[ast.BoolConst(True), ast.BoolConst(False)])
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        with self.assertRaises(AssertionError):
            out = [s for s in engine.visit(node, state = st)]
            
    def test_no_while(self):
        prg1 = """
        havoc x;
        if x > 5 then
            skip
        else
            x := x + 1;
        assume x > 0;
        while x < 0 do
            x := x + 1
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        # for s in out:
        #     print(s)
        self.assertEqual(len(out), 2)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 2)
        self.assertTrue(all(var in s.env for s in out for var in ['x']))
        
    def test_no_while_twice(self):
        prg1 = """
        havoc x;
        while x < 0 do
            x := 1
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 2) 
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 2)
        self.assertTrue(all(var in s.env for s in out for var in ['x']))  
        
    def test_no_else(self):
        prg1 = """
        havoc x;
        assume x > 5;
        if x > 5 then
            skip
        else
            x := x + 1
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        # for s in out:
        #     print(s)
        self.assertEqual(len(out), 1)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 1)
        self.assertTrue(all(var in s.env for s in out for var in ['x'])) 
        
    @patch('sys.argv', ['int.py', os.path.join(os.path.dirname(__file__), 'test1.prg')])
    @patch('sys.stdout', new_callable=StringIO)
    def test_main(self, mock_stdout):
        concolic_incremental.main()
        output = mock_stdout.getvalue().strip()
        print(output)
        self.assertIsNotNone(output)

    def test_symstate(self):
        solver = z3.Solver()
        st = concolic_incremental.ConcolicState(solver)
        self.assertEqual(st._solver, solver)
        prg1 = """
        havoc x;
        assume x > 5
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)
        self.assertIsNotNone(repr(st))
        self.assertIsNotNone(st.to_smt2())
        st = concolic_incremental.ConcolicState()
        st.env['x'] = z3.FreshInt("x")
        st.add_pc(st.env['x'] > 5)
        st.add_pc(st.env['x'] < 5)
        self.assertIsNone(st.pick_concrete())
        st.mk_error()
        self.assertTrue(st.is_error())

    def test_assume_triggers_mk_error(self):
        prg1 = """
        havoc x;
        assume x > 5;
        assert x < 0
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 0)
        self.assertTrue(all(var in s.env for s in out for var in ['x'])) 


    def test_no_then(self):
        prg1 = """
        havoc x;
        assume x < 5;
        if x > 5 then
            skip
        else
            x := x + 1
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        # for s in out:
        #     print(s)
        self.assertEqual(len(out), 1)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 1)
        self.assertTrue(all(var in s.env for s in out for var in ['x']))


    def test_simple_whileloop(self):
        prg1 = "havoc x; while x < 5 do x := x + 1"

        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        # for s in out:
        #     print(s)
        self.assertEqual(len(out), 11)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 11)
        self.assertTrue(all(var in s.env for s in out for var in ['x']))


    def test_assert_with_unsat_error_path(self):
        prg = """
        havoc x;
        assume x = 5;
        assert x = 5
        """
        ast1 = ast.parse_string(prg)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)
        out_no_error = [s for s in out if not s.is_error()]
        self.assertEqual(len(out_no_error), 1)
        self.assertTrue(all(var in s.env for s in out for var in ['x']))


    def test_diverges(self):
        prg1 = """
        havoc x, y, z;

        while x > 0 do {
            if y < 5 then {
                z := z + 1;
                if z = 3 then {
                    y := y + 2
                } else {
                    y := y + 1
                }
            } else {
                while z > 0 do {
                    z := z - 1
                };
                x := x - 1
            }
        };
        x := x + y + z
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 606)

        
    def test_execution_engine_diverges(self):
        prg1 = """
        havoc x, y;
        while x > 5 do {
            while x < y do {
                y := y / 2 - 1
            }; 
            x := x - 2
        }
        """
        ast1 = ast.parse_string(prg1)
        engine = concolic_incremental.ConExec()
        st = concolic_incremental.ConcolicState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 615)
