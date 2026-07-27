import tempfile
import unittest
from pathlib import Path

from proofmatch.document import parse_validated_markdown
from proofmatch.models import DocumentBlock, DocumentIndex
from proofmatch.search import prepare_rerank_payload, search_candidates


class SearchTests(unittest.TestCase):
    def test_single_document_segment_fills_requested_candidate_limit(self):
        with tempfile.TemporaryDirectory() as tmp:
            dataset = Path(tmp) / "data.jsonl"
            dataset.write_text(
                "".join(
                    '{"id":"T.%d","title":"Switching candidate %d",'
                    '"statement_informal":"DNF restriction decision tree",'
                    '"formal_statement":"","proof":""}\n' % (index, index)
                    for index in range(12)
                ),
                encoding="utf-8",
            )
            index = DocumentIndex(
                "abcdef1234567890",
                (
                    DocumentBlock(
                        "pdf-abcdef123456-p001-b001",
                        1,
                        1,
                        "heading",
                        "Switching Lemma",
                        "DNF restriction decision tree",
                        1.0,
                    ),
                ),
                (),
            )

            candidates = search_candidates(index, dataset, limit=12)

            self.assertEqual(len(candidates), 12)

    def test_live_lecture_fixture_retrieves_main_switching_lemma(self):
        fixture = Path("blueprint/src/references/switching-lemma.md")
        if not fixture.exists():
            self.skipTest("validated live fixture has not been generated")
        index = parse_validated_markdown(fixture)

        candidates = search_candidates(
            index, Path("dataset/tcslib_theorems.jsonl"), limit=12
        )

        self.assertIn(
            "SwitchingLemma2.switching_lemma",
            [candidate.lean_name for candidate in candidates],
        )

    def test_exact_document_title_beats_helper_with_matching_namespace(self):
        with tempfile.TemporaryDirectory() as tmp:
            dataset = Path(tmp) / "data.jsonl"
            dataset.write_text(
                '{"id":"SwitchingLemma2.helper","title":"Canonical helper",'
                '"statement_informal":"canonical decision tree bad restriction path",'
                '"formal_statement":"","proof":""}\n'
                '{"id":"SwitchingLemma2.switching_lemma",'
                '"title":"Switching Lemma -- Lean statement",'
                '"statement_informal":"DNF width restriction bound",'
                '"formal_statement":"","proof":""}\n',
                encoding="utf-8",
            )
            index = DocumentIndex(
                "abcdef123456",
                (
                    DocumentBlock(
                        "pdf-abcdef123456-p001-b001", 1, 1, "heading",
                        "The Switching Lemma", "## The Switching Lemma", 1,
                    ),
                    DocumentBlock(
                        "pdf-abcdef123456-p001-b002", 1, 2, "theorem",
                        "Theorem 1", "DNF width restriction bound", 1,
                    ),
                    DocumentBlock(
                        "pdf-abcdef123456-p001-b003", 1, 3, "proof",
                        "Proof", "canonical decision tree bad restriction path", 1,
                    ),
                ),
                (),
            )

            candidates = search_candidates(index, dataset, limit=1)

            self.assertEqual(
                candidates[0].lean_name,
                "SwitchingLemma2.switching_lemma",
            )

    def test_broad_document_does_not_dilute_switching_theorem_segment(self):
        index = DocumentIndex(
            "abcdef1234567890",
            (
                DocumentBlock(
                    "pdf-abcdef123456-p001-b001", 1, 1, "heading",
                    "Håstad's Switching Lemma", "Håstad's Switching Lemma", 1.0,
                ),
                DocumentBlock(
                    "pdf-abcdef123456-p001-b002", 1, 2, "theorem", "Theorem 1",
                    "DNF width w random s-restriction bad restrictions "
                    "DTdepth greater than d probability at most (10 sigma w)^d",
                    1.0,
                ),
                DocumentBlock(
                    "pdf-abcdef123456-p001-b003", 1, 3, "proof", "Proof",
                    "canonical decision tree path encoding injection bad restrictions",
                    1.0,
                ),
                DocumentBlock(
                    "pdf-abcdef123456-p001-b004", 1, 4, "prose", "",
                    "bound the fibers and count all bad restrictions", 1.0,
                ),
                DocumentBlock(
                    "pdf-abcdef123456-p002-b001", 2, 1, "theorem", "Parity lower bound",
                    "AC0 circuit parity exponential lower bound layers fan-in",
                    1.0,
                ),
                DocumentBlock(
                    "pdf-abcdef123456-p002-b002", 2, 2, "proof", "Proof",
                    "repeat restrictions union bound collapse circuit layers",
                    1.0,
                ),
            ),
            (),
        )

        candidates = search_candidates(
            index, Path("dataset/tcslib_theorems.jsonl"), limit=12
        )
        target = next(
            candidate
            for candidate in candidates
            if candidate.lean_name == "SwitchingLemma2.switching_lemma"
        )

        self.assertEqual(
            target.document_blocks,
            (
                "pdf-abcdef123456-p001-b001",
                "pdf-abcdef123456-p001-b002",
                "pdf-abcdef123456-p001-b003",
                "pdf-abcdef123456-p001-b004",
            ),
        )

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
