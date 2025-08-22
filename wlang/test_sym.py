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

from . import ast, sym_only
import z3
import os
from unittest.mock import patch
from io import StringIO

class TestSym (unittest.TestCase):


    def test_diverge(self):
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
        engine = sym_only.SymExec()
        st = sym_only.SymState()
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
        engine = sym_only.SymExec()
        st = sym_only.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 615)
