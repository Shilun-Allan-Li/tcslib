import tempfile
import unittest
from pathlib import Path

from proofmatch.artifacts import RunStore
from proofmatch.models import ComparisonVerdict, load_typed


class RunStoreTests(unittest.TestCase):
    def test_atomic_round_trip_keeps_runs_separate_by_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            first = RunStore(Path(tmp), "abc123")
            second = RunStore(Path(tmp), "def456")

            written = first.write_json("extract", {"pages": 4})

            self.assertEqual(written, Path(tmp) / "abc123" / "extract.json")
            self.assertEqual(first.read_json("extract"), {"pages": 4})
            self.assertIsNone(second.read_json("extract"))
            self.assertFalse(written.with_suffix(".json.tmp").exists())

    def test_typed_loader_rejects_missing_required_fields(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "verdict.json"
            path.write_text('{"verdict":"same"}', encoding="utf-8")

            with self.assertRaisesRegex(ValueError, "lean_name"):
                load_typed(path, ComparisonVerdict)

    def test_typed_loader_rejects_unknown_fields(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "verdict.json"
            path.write_text(
                """
                {
                  "lean_name": "T.foo",
                  "document_blocks": ["pdf-a-p001-b001"],
                  "verdict": "same",
                  "confidence": 0.9,
                  "differences": [],
                  "evidence": [],
                  "unexpected": true
                }
                """,
                encoding="utf-8",
            )

            with self.assertRaisesRegex(ValueError, "unexpected"):
                load_typed(path, ComparisonVerdict)


if __name__ == "__main__":
    unittest.main()
