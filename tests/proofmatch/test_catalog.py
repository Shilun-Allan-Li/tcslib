import tempfile
import unittest
from pathlib import Path

from proofmatch.catalog import load_blueprint_bindings, load_blueprint_candidates


class CatalogTests(unittest.TestCase):
    def test_collects_each_blueprint_lean_name(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "A.tex").write_text(
                "\\begin{theorem}\n\\lean{A.one, A.two}\n\\end{theorem}\n",
                encoding="utf-8",
            )
            self.assertEqual(
                set(load_blueprint_bindings(root)), {"A.one", "A.two"}
            )

    def test_duplicate_binding_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "A.tex").write_text(
                "\\begin{theorem}\n\\lean{A.one}\n\\end{theorem}\n",
                encoding="utf-8",
            )
            (root / "B.tex").write_text(
                "\\begin{lemma}\n\\lean{A.one}\n\\end{lemma}\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "multiple blueprint"):
                load_blueprint_bindings(root)

    def test_dataset_is_filtered_to_blueprint_names(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            tex = root / "A.tex"
            tex.write_text(
                "\\begin{theorem}\n\\lean{A.one}\n\\end{theorem}\n",
                encoding="utf-8",
            )
            dataset = root / "data.jsonl"
            dataset.write_text(
                '{"id":"A.one","title":"One","statement_informal":"one",'
                '"formal_statement":"True","proof":"by trivial"}\n'
                '{"id":"A.outside","title":"Outside","statement_informal":"outside",'
                '"formal_statement":"True","proof":"by trivial"}\n',
                encoding="utf-8",
            )
            candidates = load_blueprint_candidates(
                dataset, load_blueprint_bindings(root)
            )
            self.assertEqual([item.lean_name for item in candidates], ["A.one"])


if __name__ == "__main__":
    unittest.main()
