import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))

from share_construction import find_sites


class HaveSitesTest(unittest.TestCase):
    def test_nested_have_in_lambda_proof(self):
        lines = [
            "example : True := by",
            "  have outer :",
            "      True → True := fun h ↦ by -- local proof",
            "    have inner : True := by",
            "      exact h",
            "    exact inner",
            "  have direct :",
            "      True → True := by",
            "    exact outer",
            "  exact direct trivial",
        ]
        decls = {"example": {"theorem": "example", "first_line": 1, "last_line": len(lines)}}
        sites = list(find_sites("Example", lines, decls, minimum=1))
        self.assertEqual([(s.start, s.assignment, s.end) for s in sites], [(3, 3, 5), (6, 7, 9)])

    def test_calc_step_does_not_own_enclosing_have(self):
        lines = [
            "example (a b : Nat) (h : a = b) : a = b := by",
            "  have chain :",
            "      a = b := calc -- the next assignment belongs to a step",
            "    a = b := by",
            "      have inner : a = b := by",
            "        exact h",
            "      exact inner",
            "  exact chain",
        ]
        decls = {"example": {"theorem": "example", "first_line": 1, "last_line": len(lines)}}
        sites = list(find_sites("Example", lines, decls, minimum=1))
        self.assertEqual([(s.start, s.assignment, s.end) for s in sites], [(4, 4, 6)])
