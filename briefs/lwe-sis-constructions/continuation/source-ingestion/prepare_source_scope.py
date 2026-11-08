"""Prepare an owned source-validation inventory without models, builds or ingestion.

Run from any directory with python3 -I. This reads only the campaign's frozen
source files, historical inventories and its own earlier primary-source archive.
The output is preparation metadata, not an approved proofmatch dataset/result.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BRIEF = ROOT / "briefs/lwe-sis-constructions"
SOURCE = "6eec97be8f54d9990340900a5595dab32fb477f5"
ARCHIVE = ROOT.parent / "tcslib-lwe-sis-phase1/.lake/primary-sources"
INVENTORIES = [
    "gates/00-foundations/evidence/source-declarations.json",
    "gates/02-construction-core/evidence/new-source-declarations.json",
    "gates/04-encoding-adapters/evidence/source-declarations.json",
]
CITATION = re.compile(r"\[(Pei16|Wu24|PS10|AB09)(?:,\s*[^\]]+)?\]")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    declarations = []
    inventory_inputs = []
    for relative in INVENTORIES:
        raw = (BRIEF / relative).read_bytes()
        rows = json.loads(raw)
        inventory_inputs.append({"path": str((BRIEF / relative).relative_to(ROOT)),
                                 "sha256": sha(raw), "declarations": len(rows)})
        declarations.extend({key: row[key] for key in ("module", "kind", "name")}
                            for row in rows)
    assert len(declarations) == len({row["name"] for row in declarations}) == 143
    modules = []
    for module in sorted({row["module"] for row in declarations}):
        relative = module + ".lean"
        raw = (ROOT / relative).read_bytes()
        frozen = subprocess.check_output(["git", "show", SOURCE + ":" + relative],
                                         cwd=ROOT)
        assert raw == frozen, relative
        text = raw.decode("utf-8")
        citations = [{"tag": match[1], "text": match[0],
                      "line": text.count("\n", 0, match.start()) + 1}
                     for match in CITATION.finditer(text)]
        modules.append({"path": relative, "bytes": len(raw), "sha256": sha(raw),
                        "citations": citations,
                        "declarations": [row for row in declarations
                                         if row["module"] == module]})
    assert len(modules) == 19

    extraction = json.loads((HERE / "raw-extraction-receipt.json").read_text())
    sources = []
    for row in extraction["sources"]:
        pdf = ARCHIVE / Path(row["source_pdf"]).name
        raw_md = ARCHIVE / Path(row["raw_path"]).name
        pdf_bytes, raw_bytes = pdf.read_bytes(), raw_md.read_bytes()
        assert sha(pdf_bytes) == row["source_sha256"], pdf
        assert sha(raw_bytes) == row["raw_sha256"], raw_md
        text = raw_bytes.decode("utf-8")
        assert f"<!-- source-pdf-sha256: {row['source_sha256']} -->" in text
        pages = [int(n) for n in re.findall(r"<!-- pdf-page: (\d+) -->", text)]
        assert pages == list(range(1, row["page_count"] + 1)), raw_md
        sources.append({"document": pdf.stem,
                        "tag": "Pei16" if pdf.stem.startswith("peikert") else "Wu24",
                        "pdf_path": str(pdf), "pdf_bytes": len(pdf_bytes),
                        "pdf_sha256": sha(pdf_bytes), "raw_path": str(raw_md),
                        "raw_bytes": len(raw_bytes), "raw_sha256": sha(raw_bytes),
                        "raw_pages_verified": len(pages),
                        "suspect_pages": row["suspect_pages"],
                        "validated_markdown": False, "approved_matching": False})
    assert sum(row["raw_pages_verified"] for row in sources) == 196
    proposal = json.loads((HERE / "registry-proposal.json").read_text())
    assert sha((ROOT / proposal["target"]).read_bytes()) == proposal["baseline_sha256"]
    result = {
        "source_pin": SOURCE,
        "purpose": "Owned scope and exact input identities for a future source-validation job",
        "not_an_approved_proofmatch_result": True,
        "citation_scan_scope": "All literal tags in module text, including reference headers; not declaration-to-block matches",
        "source_documents_in_scope": ["Pei16", "Wu24"],
        "existing_context_tags_only": ["PS10", "AB09"],
        "inventory_inputs": inventory_inputs,
        "source_modules": len(modules),
        "source_declarations": len(declarations),
        "source_declaration_kinds": dict(Counter(row["kind"] for row in declarations)),
        "literal_citation_occurrences": dict(Counter(c["tag"] for m in modules
                                                     for c in m["citations"])),
        "sources": sources,
        "modules": modules,
        "shared_registry_proposal_applied": False,
        "blueprint_or_dataset_changed": False,
        "source_policy_closed": False,
        "external_job_selected_or_dispatched_by_this_preparation": False,
    }
    (HERE / "source-validation-scope.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"source_modules": len(modules), "owned_declarations": len(declarations),
                      "primary_pdfs_rehashed": len(sources), "raw_pages_verified": 196,
                      "source_policy_closed": False}))


if __name__ == "__main__":
    main()
