#!/usr/bin/env python3
"""Record the source/native-reviewed complete 208-row base explicit scan.

Run with python3 -I. No Lean or subprocess is invoked. The ten open lexical
rows and the false-local namespace row have explicit source-based corrections.
"""
from __future__ import annotations
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "evidence/probes/Rule10/final2"
BASE = ROOT / "evidence/probes/Rule10/BaseTree"
sys.dont_write_bytecode = True


def need(ok, why):
    if not ok:
        raise RuntimeError(why)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def relative(path):
    return path.relative_to(ROOT).as_posix()


def main():
    old_plan_path = ROOT / "evidence/probes/Rule10/final1/base-scan-plan.json"
    plan_path = OUT / "base-scan-plan.json"
    native_path = OUT / "base-explicit-scan.json"
    plan, native = read(plan_path), read(native_path)
    need(plan["items"] == read(old_plan_path)["items"] and len(plan["items"]) == 208,
         "manually reviewed row/source inventory changed")
    need(plan["side"] == native["side"] == "base" and plan["edition"] == native["edition"] == "final2",
         "scan side/edition differs")
    need(len(native["items"]) == 208 and
         [{k: row[k] for k in original} for row, original in zip(native["items"], plan["items"])] == plan["items"],
         "native inventory differs from source plan")
    log = ROOT / native["native_log"]
    need(sha(log) == native["native_log_sha256"], "native scan log differs")
    text = log.read_text()
    table = [json.loads(line[10:]) for line in text.splitlines() if line.startswith("SCAN-CAND ")]
    counts = [int(line[11:]) for line in text.splitlines() if line.startswith("SCAN-COUNT ")]
    need(table == native["native_candidates"] and counts == [len(table)], "native kind/home table differs")
    result_path = ROOT / "evidence/logs/rule10/final2/scan-base/results.jsonl"
    records = [json.loads(line) for line in result_path.read_text().splitlines() if line.strip()]
    records = [r for r in records if r["log"] == native["native_log"]]
    need(len(records) == 1 and records[0]["exit_code"] == 0 and records[0]["source_unchanged"] is True and
         records[0]["source_sha256"] == records[0]["source_after_sha256"] == plan["source_sha256"],
         "native kind/home probe did not pass unchanged")
    draft_tool = ROOT / "evidence/tools/base_scan_review.py"
    spec = importlib.util.spec_from_file_location("dl_crh_source_reviewed_base_bindings", draft_tool)
    source_review = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source_review)
    state = read(ROOT / "evidence/probes/Rule10/base-state.json")
    sources = {path: (BASE / path).read_text().splitlines() for path in {r["path"] for r in plan["items"]}}
    for path in sources:
        need(sha(BASE/path) == state["source_hashes"][path], "exact base source differs")
    opened = {2, 4, 5, 6, 114, 115, 130, 131, 133, 134}
    need({i for i, row in enumerate(native["items"], 1) if row["resolution"] in {"UNRESOLVED", "AMBIGUOUS"}} == opened,
         "native open-row set changed; manual review required")
    rows = []
    for index, (item, scan) in enumerate(zip(plan["items"], native["items"]), 1):
        lines = sources[item["path"]]
        row = dict(item, id=f"B{index:03d}", status="REVIEWED", source_sha256=state["source_hashes"][item["path"]],
            scanner_resolution=scan["resolution"], scanner_candidates=scan["candidates"],
            scanner_foreign_definitions=scan["foreign_definitions"], selected_native_candidates=[],
            source_context=[dict(line=n, text=lines[n-1]) for n in range(max(1,item["line"]-2),min(len(lines),item["line"]+2)+1)])
        if index in source_review.LOCALS:
            line, name = source_review.LOCALS[index]
            need(item["head"] == name and name in lines[line-1], "local binding changed")
            need(scan["resolution"] in {"LOCAL_BINDER_OR_MEMBER", "UNRESOLVED"} and not scan["foreign_definitions"],
                 "local/native classification differs")
            row.update(classification="LOCAL_PROOF", final_native_disposition="LOCAL_PROOF_BINDING_CONFIRMED",
                disposition="The explicit tactic item is the local equality/proof binding at the recorded source line; it requests no global definition body.",
                binding_evidence=dict(line=line,text=lines[line-1]))
        elif index == 114:
            need(item["head"] == "show" and "from (hs z).2" in item["item"] and "obtain ⟨g, hg, hs⟩" in lines[685],
                 "inline local proof changed")
            row.update(classification="INLINE_LOCAL_PROOF", final_native_disposition="INLINE_LOCAL_PROOF_CONFIRMED",
                disposition="show is Lean syntax; this inline equality is proved by the local hypothesis (hs z).2 obtained at line 686. Global symbols in the proposition are term references, not explicit body unfolding.",
                binding_evidence=dict(line=686,text=lines[685]))
        else:
            if index == 153:
                need(item["head"] == "ZMod.val_natCast" and scan["resolution"] == "LOCAL_BINDER_OR_MEMBER",
                     "namespace correction row changed")
                selected = [c for c in table if c["name"] == "ZMod.val_natCast"]
                need(len(selected) == 1 and selected[0]["kind"] == "theorem" and selected[0]["home"] == "Mathlib.Data.ZMod.Basic",
                     "qualified ZMod reader kind/home differs")
                row["manual_correction"] = "The binder regex misclassified ZMod from the type at line 929. No local declaration binds the name ZMod; line 935 uses the qualified global theorem. Exact native identity/kind/home is recorded."
                row["correction_source_evidence"] = [dict(line=n,text=lines[n-1]) for n in range(929,936)]
            else:
                need(scan["resolution"] == "RESOLVED" and len(scan["candidates"]) == 1,
                     "global row lacks a unique native/source resolution")
                selected = scan["candidates"]
            candidate = selected[0]
            row["selected_native_candidates"] = selected
            if candidate["kind"] == "def":
                need(candidate["home"] == item["module"], "foreign ordinary definition requires separate inherited disposition")
                row.update(classification="OWN_DEFINITION", final_native_disposition="OWN_DEFINITION_BODY_ALLOWED",
                    disposition="The native constant's home is this exact source module, so its own defining body is available under Rule 10. This occurrence already exists at the issue base.")
            else:
                need(candidate["kind"] == "theorem" and (not candidate["private"] or candidate["home"] == item["module"]),
                     "non-theorem or foreign private result requires explicit review")
                row.update(classification="THEOREM_READER", final_native_disposition="THEOREM_READER_CONFIRMED",
                    disposition="The selected native constant is a theorem; the tactic uses its published equality/result rather than a foreign ordinary definition body.")
        need(not scan["foreign_definitions"], "native foreign-definition candidate requires individual inherited disposition")
        rows.append(row)
    kinds = dict(Counter(row["classification"] for row in rows))
    need(kinds == {"LOCAL_PROOF":31,"INLINE_LOCAL_PROOF":1,"OWN_DEFINITION":36,"THEOREM_READER":140}, "review category counts changed")
    result = dict(status="COMPLETE", reviewed_all_rows=True, pending_rows=0, new_foreign_definition_hits=0,
        side="base", edition="final2", row_count=208, classification_counts=kinds,
        plan=relative(plan_path), plan_sha256=sha(plan_path), native_scan=relative(native_path), native_scan_sha256=sha(native_path),
        native_log=native["native_log"], native_log_sha256=sha(log), native_results=relative(result_path),
        prior_plan=relative(old_plan_path), prior_plan_sha256=sha(old_plan_path), identical_prior_inventory=True,
        local_binding_review_tool=relative(draft_tool), local_binding_review_tool_sha256=sha(draft_tool),
        source_hashes={path:state["source_hashes"][path] for path in sorted(sources)},
        native_open_rows_reviewed=[f"B{i:03d}" for i in sorted(opened)], lexical_namespace_corrections=["B153"],
        foreign_definition_candidate_items=[], inherited_foreign_definition_hits=[],
        own_definition_rows=[row["id"] for row in rows if row["classification"]=="OWN_DEFINITION"],
        limitations=["The native scanner retains its original lexical classifications; manual source corrections are separately recorded.",
            "Baseline new-hit count is zero by base semantics; this review additionally found zero actual foreign ordinary-definition heads.",
            "This is explicit tactic-item review only. The independent whole-file seals cover implicit TCSlib body reads."], rows=rows)
    (OUT/"base-explicit-manual-review.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    md=["# Complete base explicit scan manual review", "", "Status: `COMPLETE`; all 208 rows reviewed, zero pending rows, zero foreign ordinary-definition heads.",
        "", "The exact final2 plan/native table and original source hashes are bound in the JSON. The final1 inventory is byte-for-byte identical by row.",
        "", "Categories: 31 local proofs, one inline local proof, 36 own-definition body uses and 140 theorem readers.",
        "", "## Individual lexical corrections", "", "| Row | Item | Source evidence and completed disposition |", "|---|---|---|"]
    for index in sorted(opened|{153}):
        row=rows[index-1]; evidence=row.get("binding_evidence")
        details=("Binding at original line "+str(evidence["line"])+": "+evidence["text"]) if evidence else row["manual_correction"]
        md.append(f"| {row['id']} | `{row['head']}` | {details.replace('|','\\|')} |")
    md += ["", "## Every source item", "", "| ID | Source | Head | Completed disposition | Native constant kind/home |", "|---|---|---|---|---|"]
    for row in rows:
        selected=row["selected_native_candidates"]
        identity=(selected[0]["name"]+"; "+selected[0]["kind"]+"; "+selected[0]["home"]) if selected else "Source-local proof/syntax"
        md.append(f"| {row['id']} | {row['path']}:{row['line']} | `{row['head']}` | {row['final_native_disposition']} | {identity} |")
    md += ["", "All native scanner open-row classifications remain preserved in JSON, alongside exact binding evidence or the qualified ZMod theorem correction. No source item received a blanket clearance."]
    (OUT/"base-explicit-manual-review.md").write_text("\n".join(md)+"\n")
    print(json.dumps(dict(status="COMPLETE",rows=len(rows),classification_counts=kinds,foreign_definition_heads=0),indent=2))


if __name__ == "__main__":
    main()
