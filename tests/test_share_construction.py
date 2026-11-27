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
