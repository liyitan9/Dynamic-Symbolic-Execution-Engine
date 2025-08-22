import unittest

from . import ast, int, concolic, sym_org
from .concolic import ConcolicExec


class TestConcolic(unittest.TestCase):
    def test_one(self):
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
        engine = ConcolicExec()
        sstate = sym_org.SymState()
        cstate = int.State()
        out = [s for s in engine.run(ast1, cstate, sstate)]

        for i, (c, s) in enumerate(out):
            print(f"\n=== Output State {i} ===")
            print("Concrete state:", c)
            print("Symbolic state:", s)
            print("Error:", s.is_error())

        self.assertEqual(len(out), 2)
        # s = out[0]
        # self.assertIn("x", s.env)
        # self.assertEqual(executor.feasible_paths, 2)

    def test_two(self):
        prg1 = """
        havoc a;
        b := 2;
        c := 3;
        assert a > b
        """

        ast1 = ast.parse_string(prg1)
        engine = ConcolicExec()
        sstate = sym_org.SymState()
        cstate = int.State()
        out = [s for s in engine.run(ast1, cstate, sstate)]

        for i, (c, s) in enumerate(out):
            print(f"\n=== Output State {i} ===")
            print("Concrete state:", c)
            print("Symbolic state:", s)
            print("Error:", s.is_error())

        self.assertEqual(len(out), 2)


if __name__ == "__main__":
    unittest.main()
