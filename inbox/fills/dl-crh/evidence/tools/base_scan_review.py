#!/usr/bin/env python3
"""Prepare the source-reviewed base explicit-scan draft; never invokes Lean.

Run as python3 -I evidence/tools/base_scan_review.py. Global names remain
pending native kind/home review. This tool owns only the base review outputs.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "evidence/probes/Rule10/final1"
PLAN = OUT / "base-scan-plan.json"
BASE = ROOT / "evidence/probes/Rule10/BaseTree"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


# Manually checked binding locations in the exact original Candidates source.
# Keys are stable one-based row identities from the issued 208-item base plan.
LOCALS = {
    2: (157, "ha"), 4: (163, "ha"), 5: (163, "hb"), 6: (163, "hc"),
    13: (248, "hl"), 16: (248, "hl"), 30: (280, "hl"), 37: (303, "h1"),
    54: (459, "h3"), 55: (461, "h2"), 56: (461, "h2"), 57: (459, "h3"),
    58: (463, "hg"), 59: (463, "hg"), 60: (459, "h3"), 61: (463, "hg"),
    62: (461, "h2"), 63: (459, "h3"), 93: (626, "hacc"), 115: (709, "he"),
    130: (755, "hvdef"), 131: (757, "hs"), 133: (755, "hvdef"), 134: (757, "hs"),
    139: (764, "henc"), 141: (764, "henc"), 155: (924, "hofn"),
    159: (938, "hX"), 160: (943, "hY"), 170: (990, "hY"), 172: (1001, "hw"),
}


def main():
    plan = json.loads(PLAN.read_text())
    if len(plan["items"]) != 208 or plan["side"] != "base":
        raise RuntimeError("base plan scope changed; manual row bindings need review")
    native_path = OUT / "base-explicit-scan.json"
    native = json.loads(native_path.read_text()) if native_path.exists() else None
    if native is not None and [dict((k, r[k]) for k in plan["items"][i]) for i, r in enumerate(native["items"])] != plan["items"]:
        raise RuntimeError("native inventory differs from reviewed plan")
    sources = {}
    rows = []
    for index, item in enumerate(plan["items"], 1):
        source = BASE / item["path"]
        lines = sources.setdefault(item["path"], source.read_text().splitlines())
        snippet = [{"line": n, "text": lines[n-1]} for n in range(max(1, item["line"]-2), min(len(lines), item["line"]+2)+1)]
        row = dict(item, id=f"B{index:03d}", source_sha256=sha(source), source_context=snippet,
                   status="PENDING_NATIVE_KIND_HOME", classification="GLOBAL_PENDING_NATIVE",
                   disposition="Pending native constant kind/home; no global clearance inferred from spelling.")
        if index in LOCALS:
            binding_line, name = LOCALS[index]
            if item["head"] != name or name not in lines[binding_line-1]:
                raise RuntimeError("manually reviewed local binding changed: " + row["id"])
            row.update(status="REVIEWED_SOURCE", classification="LOCAL_PROOF",
                       disposition="Local equality/proof binding, not a global definition-body request.",
                       binding_evidence={"line": binding_line, "text": lines[binding_line-1]})
        elif index == 114:
            if item["head"] != "show" or "from (hs z).2" not in item["item"]:
                raise RuntimeError("inline-proof row changed")
            row.update(status="REVIEWED_SOURCE", classification="INLINE_LOCAL_PROOF",
                       disposition="The show-expression supplies the local proof (hs z).2; show is syntax. Global names in its proposition are term references, not explicit unfolding requests.",
                       binding_evidence={"line": 705, "text": "rw [show ... from (hs z).2]"})
        else:
            own = [d for d in plan["declarations"][item["path"]]
                   if d["name"] == item["head"] or d["name"].endswith("." + item["head"])]
            if len(own) == 1:
                d = own[0]
                row["provisional_source_hint"] = {"name": d["name"], "kind": d["kind"], "line": d["line"],
                    "category": "OWN_DEFINITION" if d["kind"] in {"def", "abbrev"} else "OWN_READER_OR_RESULT"}
            else:
                row["provisional_source_hint"] = {"category": "GLOBAL_READER_OR_RESULT_CANDIDATE",
                    "note": "Spelling is only an inventory hint; native kind/home still required."}
        if native is not None:
            n = native["items"][index-1]
            row.update(native_resolution=n["resolution"], native_candidates=n["candidates"],
                       native_foreign_definitions=n["foreign_definitions"])
        rows.append(row)
    pending = sum(row["status"].startswith("PENDING") for row in rows)
    output = dict(status="PENDING_MANUAL_NATIVE_REVIEW" if native else "PENDING_NATIVE_KIND_HOME",
        reviewed_all_rows=False, pending_rows=pending, reviewed_source_rows=len(rows)-pending,
        new_foreign_definition_hits=None, inherited_foreign_definition_hits=[],
        side="base", edition="final1", row_count=len(rows), plan=str(PLAN.relative_to(ROOT)),
        plan_sha256=sha(PLAN), native_scan=str(native_path.relative_to(ROOT)) if native else None,
        native_scan_sha256=sha(native_path) if native else None,
        source_hashes={p: sha(BASE/p) for p in sorted(sources)},
        limitations=["Draft only: every global row remains pending native kind/home and manual review.",
            "Local proof bindings and the inline show-expression were checked against exact base source.",
            "Every native candidate/hit/unresolved result is retained when available; source lexical resolution is not the Lean elaborator."],
        rows=rows)
    (OUT/"base-explicit-manual-review.json").write_text(json.dumps(output,indent=2,ensure_ascii=False)+"\n")
    md=["# Base explicit scan manual review draft", "", "Status: `"+output["status"]+"`. This draft grants no global clearance.",
        "",f"All {len(rows)} rows retained; {len(rows)-pending} source-reviewed local/inline proof rows, {pending} global rows pending native kind/home review.",
        "", "| ID | Source | Tactic item | Source disposition | Native state |", "|---|---|---|---|---|"]
    for row in rows:
        item=row["item"].replace("|","\\|").replace("\n"," ")
        native_state=row.get("native_resolution","NOT_RUN")
        md.append(f"| {row['id']} | {row['path']}:{row['line']} | `{item}` | {row['classification']} | {native_state} |")
    md += ["", "The JSON retains exact source hashes, context lines, local-binding evidence, provisional own-declaration hints, and every native candidate when available.",
        "All global hints are provisional. After native review, preserve every foreign definition hit and every unresolved/ambiguous-row disposition, and record inherited base findings separately from new final findings."]
    (OUT/"base-explicit-manual-review.md").write_text("\n".join(md)+"\n")
    print(f"Wrote {len(rows)} base review rows: {len(rows)-pending} source-reviewed; {pending} pending native review.")


if __name__ == "__main__":
    main()
