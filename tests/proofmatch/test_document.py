import tempfile
import unittest
from decimal import Decimal
from pathlib import Path

from proofmatch.budget import Budget
from proofmatch.document import (
    parse_validated_markdown,
    repair_document,
    stable_block_id,
)


class FakeAgent:
    def __init__(self):
        self.calls = []

    def run(self, prompt_name, payload, schema_name=None, images=()):
        self.calls.append((prompt_name, payload, tuple(images)))
        if prompt_name == "cleanup":
            return {
                "blocks": [
                    {
                        "page": 1,
                        "sequence": 1,
                        "kind": "theorem",
                        "title": "Theorem 1",
                        "markdown": "## Theorem 1\n$A \\to B$.",
                        "confidence": 0.99,
                    },
                    {
                        "page": 2,
                        "sequence": 1,
                        "kind": "proof",
                        "title": "Proof",
                        "markdown": "## Proof\nThe value is $x ? 1$.",
                        "confidence": 0.5,
                    },
                ],
                "ambiguities": [
                    {"page": 2, "sequence": 1, "reason": "comparison symbol"}
                ],
            }
        return {
            "corrections": [
                {
                    "page": 2,
                    "sequence": 1,
                    "markdown": "## Proof\nThe value is $x \\leq 1$.",
                    "confidence": 0.98,
                    "unresolved_reason": None,
                }
            ]
        }


class DocumentTests(unittest.TestCase):
    def test_parser_recovers_bold_theorem_and_proof_kinds(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "notes.md"
            path.write_text(
                "<!-- source-pdf-sha256: abcdef1234567890 -->\n"
                '<a id="pdf-abcdef123456-p001-b001"></a>\n'
                "<!-- pdf-source: page=1; block=1; confidence=0.99 -->\n"
                "**Theorem 1.** Switching bound.\n"
                '<a id="pdf-abcdef123456-p001-b002"></a>\n'
                "<!-- pdf-source: page=1; block=2; confidence=0.98 -->\n"
                "**Proof.** Encode bad restrictions.\n",
                encoding="utf-8",
            )

            index = parse_validated_markdown(path)

            self.assertEqual([block.kind for block in index.blocks], ["theorem", "proof"])

    def test_switching_lemma_section_heading_stays_a_heading(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "notes.md"
            path.write_text(
                "<!-- source-pdf-sha256: abcdef1234567890 -->\n"
                '<a id="pdf-abcdef123456-p001-b001"></a>\n'
                "<!-- pdf-source: page=1; block=1; confidence=0.99 -->\n"
                "## 2. The Switching Lemma\n",
                encoding="utf-8",
            )

            index = parse_validated_markdown(path)

            self.assertEqual(index.blocks[0].kind, "heading")

    def test_block_id_is_stable_and_heading_independent(self):
        self.assertEqual(
            stable_block_id("abcdef1234567890", 2, 3),
            "pdf-abcdef123456-p002-b003",
        )

    def test_only_ambiguous_page_is_rendered_and_validated(self):
        agent = FakeAgent()
        rendered = []

        def renderer(pdf, page, output):
            rendered.append(page)
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(b"png")
            return output

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            raw = root / "notes.raw.md"
            raw.write_text(
                """
<!-- source-pdf-sha256: abcdef1234567890 -->
<!-- pdf-page: 1 -->
Theorem 1 A -> B

<!-- pdf-page: 2 -->
Proof x ? 1
""".lstrip(),
                encoding="utf-8",
            )
            output = root / "notes.md"
            pdf = root / "notes.pdf"
            pdf.write_bytes(b"pdf")

            index = repair_document(
                raw,
                output,
                agent,
                Budget(Decimal("1.00")),
                pdf_path=pdf,
                renderer=renderer,
            )

            self.assertEqual(rendered, [2])
            self.assertEqual([call[0] for call in agent.calls], ["cleanup", "visual_validate"])
            self.assertEqual(len(agent.calls[1][2]), 1)
            self.assertIn("$x \\leq 1$", output.read_text(encoding="utf-8"))
            self.assertEqual(index.blocks[1].confidence, 0.98)

    def test_cleanup_rejects_duplicate_page_sequence(self):
        agent = FakeAgent()
        original = agent.run

        def duplicate(prompt_name, payload, schema_name=None, images=()):
            value = original(prompt_name, payload, schema_name, images)
            if prompt_name == "cleanup":
                value["blocks"].append(dict(value["blocks"][0]))
            return value

        agent.run = duplicate
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            raw = root / "notes.raw.md"
            raw.write_text(
                "<!-- source-pdf-sha256: abcdef1234567890 -->\n"
                "<!-- pdf-page: 1 -->\ntext\n"
                "<!-- pdf-page: 2 -->\nmore text\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "duplicate block"):
                repair_document(
                    raw,
                    root / "notes.md",
                    agent,
                    Budget(Decimal("1.00")),
                )


if __name__ == "__main__":
    unittest.main()
