import unittest
from pathlib import Path

from scripts.blueprint_enumerate import extract_signature
from scripts.build_dataset import split_signature


class BlueprintSignatureTests(unittest.TestCase):
    def test_retains_local_bindings_in_the_result_type(self):
        signature = "theorem sample : let x := 1; let y := x + 1; y = 2"
        self.assertEqual(split_signature(signature + " := by decide"), signature)

    def test_ignores_binder_defaults_and_nested_assignments(self):
        signature = "theorem sample (x : Nat := 1) : (let y := x; y) = x"
        self.assertEqual(split_signature(signature + " := rfl"), signature)

    def test_ignores_comments_strings_and_quoted_identifiers(self):
        signature = (
            'theorem «let := sample» :\n'
            '/- let /- := -/ := -/\n'
            '-- := let\n'
            '"let := \\"" = "let := \\""'
        )
        self.assertEqual(split_signature(signature + " := rfl"), signature)

    def test_retains_have_assignments_in_the_result_type(self):
        signature = "theorem sample : have h : True := by trivial; True"
        self.assertEqual(split_signature(signature + " := h"), signature)

    def test_character_literals_do_not_change_delimiter_depth(self):
        signature = "theorem sample' : '(' = '('"
        self.assertEqual(split_signature(signature + " := rfl"), signature)

    def test_actual_two_point_conclusions_survive_both_pipeline_stages(self):
        source = Path(__file__).resolve().parents[1] / (
            "TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/TwoPoint.lean"
        )
        lines = source.read_text().splitlines()
        for name in ("integrated_h_alpha_ineq", "two_point_ineq_general_unit"):
            with self.subTest(name=name):
                start = next(i for i, line in enumerate(lines) if
                             line.startswith(("lemma " + name, "theorem " + name)))
                end = next(i for i in range(start, len(lines)) if
                           lines[i].endswith(" := by"))
                expected = "\n".join(lines[start:end + 1]).removesuffix(" := by")
                self.assertEqual(split_signature("\n".join(lines[start:end + 4])), expected)
                self.assertEqual(extract_signature(lines, start, end + 4), expected + " :=")
                self.assertIn("Real.sqrt ((p - 1) / (q - 1))", expected)
                self.assertIn("≤", expected)


if __name__ == "__main__":
    unittest.main()
