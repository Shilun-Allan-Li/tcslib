import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts import dataset_projects as dp
from scripts import build_dataset as bd
from scripts.build_dep_graph import parse_ilean, prune_impossible_forward_refs
from scripts.dataset_splice import merge
from scripts.dataset_check import lean_check_sample
import subprocess
import os
from proofmatch.dataset_io import resolve_dataset
from scripts.blueprint_sync_deps import refresh_entry


class ProjectDatasetTests(unittest.TestCase):
    def test_spurious_forward_reference_is_audited_but_mutual_reference_is_kept(self):
        for source, end, expected in [
            ("theorem first : True := by trivial\n\ntheorem later : True := by trivial\n", 1, 1),
            ("mutual\n  def first := later\n  def later := first\nend\n", 2, 0),
        ]:
            parsed = {"module": "FABL.Test", "declarations": {
                "first": {"startLine": 1 if end == 1 else 2, "endLine": end,
                          "deps": [{"module": "FABL.Test", "name": "later"}]},
                "later": {"startLine": 3, "endLine": 3, "deps": []}}}
            with tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / "Test.lean"
                path.write_text(source)
                rejected = prune_impossible_forward_refs(parsed, path)
            self.assertEqual(len(rejected), expected)
            self.assertEqual(len(parsed["declarations"]["first"]["deps"]), 1 - expected)

    def test_dependency_refresh_preserves_prose_citations_and_ratings(self):
        text = ("\\begin{theorem}\n\\lean{FABL.foo}\n\\leanok\n\\uses{old}\n"
                "\\difficulty{3}\n\\statementsource{book}{anchor}\nThe original claim.\n\\end{theorem}")
        result = refresh_entry(text, {"FABL.foo": {"FABL.bar", "FABL.peer"}}, {"FABL.foo": {"FABL.peer"}})
        self.assertIn("\\uses{FABL.bar}", result)
        self.assertLess(result.index("\\leanok"), result.index("\\uses"))
        self.assertIn("% simultaneous-definitions: FABL.peer", result)
        self.assertIn("\\difficulty{3}\n\\statementsource{book}{anchor}\nThe original claim.", result)
        self.assertNotIn("\\uses{old}", result)
        self.assertEqual(refresh_entry(result, {"FABL.foo": {"FABL.bar", "FABL.peer"}},
                                       {"FABL.foo": {"FABL.peer"}}), result)

    def test_newer_tracked_gzip_wins_over_stale_local_jsonl(self):
        with tempfile.TemporaryDirectory() as tmp:
            plain = Path(tmp) / "data.jsonl"
            compressed = Path(tmp) / "data.jsonl.gz"
            plain.write_text("old")
            compressed.write_text("new")
            os.utime(plain, (10, 10))
            os.utime(compressed, (20, 20))
            self.assertEqual(resolve_dataset(plain), compressed)
            os.utime(plain, (30, 30))
            self.assertEqual(resolve_dataset(plain), plain)
            self.assertEqual(resolve_dataset(compressed), compressed)

    def parse(self, artifact):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Example.ilean"
            path.write_text(json.dumps(artifact))
            return parse_ilean(path)

    def test_lean_432_decl_ranges_and_five_field_usages(self):
        ref = json.dumps({"c": {"m": "FABL.Base", "n": "FABL.base"}})
        result = self.parse({
            "module": "FABL.Example", "directImports": [["FABL.Base", False]],
            "decls": {"FABL.foo": [4, 0, 8, 10, 5, 8, 5, 11],
                      "FABL.unused": [10, 0, 11, 10, 10, 8, 10, 14]},
            "references": {ref: {"usages": [[7, 0, 7, 4, "FABL.foo"]]}},
        })
        self.assertEqual(result["declarations"]["FABL.foo"], {
            "startLine": 5, "endLine": 9,
            "deps": [{"module": "FABL.Base", "name": "FABL.base"}],
        })
        self.assertIn("FABL.unused", result["declarations"])

    def test_lean_425_extended_usages_remain_supported(self):
        ref = json.dumps({"c": {"m": "Mathlib.Base", "n": "base"}})
        result = self.parse({"module": "TCSlib.Example", "references": {
            ref: {"usages": [[7, 0, 7, 4, "foo", 4, 0, 8, 10]]}}})
        self.assertEqual(result["declarations"]["foo"]["startLine"], 5)
        self.assertEqual(result["declarations"]["foo"]["deps"][0]["name"], "base")

    @patch.object(dp, "projects", return_value={"TCSlib": Path("/repo"), "FABL": Path("/other")})
    def test_sources_and_selection_keep_the_original_module_root(self, _):
        self.assertEqual(dp.source_path("FABL.Chapter01.Base"), Path("/other/FABL/Chapter01/Base.lean"))
        self.assertTrue(dp.module_matches("FABL.Chapter01.Base", ["FABL"]))
        self.assertTrue(dp.module_matches("FABL.Chapter01.Base", ["Chapter01"]))
        self.assertFalse(dp.module_matches("FABLish.Base", ["FABL"]))
        self.assertFalse(dp.is_internal("FABLish.Base"))

    @patch.object(dp, "projects", return_value={"TCSlib": Path("/repo"), "FABL": Path("/other")})
    def test_public_import_and_exposed_section_preserve_context(self, _):
        lines = ["module", "public import FABL.Base", "public import Mathlib.Data.Nat.Basic",
                 "@[expose] public section", "namespace FABL", "variable {n : Nat}",
                 "public theorem foo : n = n := rfl", "end FABL"]
        _, contexts, external = bd.parse_file_context(lines)
        self.assertEqual(external, ["import Mathlib.Data.Nat.Basic"])
        self.assertEqual(contexts[6]["variables"], ["variable {n : Nat}"])
        self.assertEqual(contexts[6]["namespace"], "FABL")
        self.assertEqual(contexts[6]["prefix"], [])
        _, items, external = bd.parse_module_items(lines)
        self.assertEqual(items[6]["ns"], "FABL")
        self.assertEqual(items[6]["vars"], ["variable {n : Nat}"])

    def test_selected_external_merge_preserves_existing_records(self):
        old = {"id": "Old.foo", "source_module": "TCSlib.Old"}
        new = {"id": "FABL.foo", "source_module": "FABL.New"}
        result, report = merge([old], {new["id"]: new}, {}, selected=True, drop_unbuilt=False)
        self.assertEqual({r["id"] for r in result}, {old["id"], new["id"]})
        self.assertEqual(report["added"], [new["id"]])

    def test_sample_checks_use_the_external_projects_environment(self):
        record = {"id": "FABL.foo", "source_module": "FABL.New",
                  "formal_statement": "import Mathlib\nexample : True := by trivial"}
        with patch.object(dp, "projects", return_value={"FABL": Path("/other")}), \
             patch("scripts.dataset_check.subprocess.run", return_value=subprocess.CompletedProcess([], 0, "")) as run:
            self.assertEqual(lean_check_sample([record], 1, 0), [])
        self.assertEqual(run.call_args.kwargs["cwd"], Path("/other"))
        self.assertEqual(run.call_args.args[0][:3], ["lake", "env", "lean"])


if __name__ == "__main__":
    unittest.main()
