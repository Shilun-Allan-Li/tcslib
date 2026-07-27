import tempfile
import unittest
from pathlib import Path

from proofmatch.models import DocumentBlock, DocumentIndex
from proofmatch.search import prepare_rerank_payload, search_candidates


class SearchTests(unittest.TestCase):
    def test_switching_lemma_is_in_bounded_candidates(self):
        index = DocumentIndex(
            source_fingerprint="abcdef1234567890",
            blocks=(
                DocumentBlock(
                    block_id="pdf-abcdef123456-p001-b001",
                    page=1,
                    sequence=1,
                    kind="heading",
                    title="Håstad's Switching Lemma",
                    markdown=(
                        "A DNF of width at most w under a random restriction "
                        "has a shallow decision tree with probability at least "
                        "one minus $(10\\sigma w)^d$."
                    ),
                    confidence=1.0,
                ),
            ),
            ambiguities=(),
        )

        candidates = search_candidates(
            index,
            Path("dataset/tcslib_theorems.jsonl"),
            limit=12,
        )

        self.assertIn(
            "SwitchingLemma2.switching_lemma",
            [candidate.lean_name for candidate in candidates],
        )

    def test_rerank_payload_excludes_full_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            dataset = Path(tmp) / "data.jsonl"
            dataset.write_text(
                '{"id":"T.foo","lean_name":"T.foo","title":"Foo",'
                '"informal_statement":"Foo theorem","statement_informal":"Foo",'
                '"formal_statement":"theorem foo : True := by sorry",'
                '"proof":"SECRET COMPLETE PROOF"}\n',
                encoding="utf-8",
            )
            index = DocumentIndex(
                "abcdef123456",
                (
                    DocumentBlock(
                        "pdf-abcdef123456-p001-b001",
                        1,
                        1,
                        "theorem",
                        "Foo",
                        "Foo theorem",
                        1.0,
                    ),
                ),
                (),
            )
            candidates = search_candidates(index, dataset, limit=1)

            payload = prepare_rerank_payload(candidates, index)

            self.assertNotIn("SECRET COMPLETE PROOF", str(payload))
            self.assertEqual(payload["candidates"][0]["lean_name"], "T.foo")


if __name__ == "__main__":
    unittest.main()
