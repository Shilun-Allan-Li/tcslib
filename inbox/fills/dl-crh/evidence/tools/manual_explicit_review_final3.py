#!/usr/bin/env python3
"""Materialize fresh final3 native/manual dispositions; no Lean or Lake."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "evidence/probes/Rule10/final3"
PLAN_PATH = HERE / "final-scan-plan.json"
NATIVE_PATH = HERE / "final-explicit-scan.json"
DRAFT_PATH = HERE / "final-explicit-manual-draft.json"
SNAPSHOT_PATH = HERE / "snapshot.json"
PREVIOUS_PATH = ROOT / "evidence/probes/Rule10/final2/final-explicit-manual-review.json"
SUPPORT_PATH = HERE / "explicit-simproc-source-evidence.json"
PREVIOUS_SUPPORT = ROOT / "evidence/probes/Rule10/final2/explicit-simproc-source-evidence.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


plan = json.loads(PLAN_PATH.read_text())
native = json.loads(NATIVE_PATH.read_text())
draft = json.loads(DRAFT_PATH.read_text())
snapshot = json.loads(SNAPSHOT_PATH.read_text())
previous = json.loads(PREVIOUS_PATH.read_text())
assert draft["plan_sha256"] == sha(PLAN_PATH)
assert draft["source_snapshot_sha256"] == sha(SNAPSHOT_PATH)
assert draft["previous_review_sha256"] == sha(PREVIOUS_PATH)
assert len(plan["items"]) == len(native["items"]) == len(draft["rows"]) == 595
assert plan["items"] == [{k: v for k, v in row.items()
                          if k not in {"resolution", "candidates", "foreign_definitions"}}
                         for row in native["items"]]
assert sha(ROOT / native["native_log"]) == native["native_log_sha256"]
assert sha(ROOT / (plan["module"] + ".lean")) == plan["source_sha256"]
assert sha(ROOT / plan["delivered_source"]) == plan["source_sha256"]

# Bind the entire frozen import closure, not only the eight changed owners.
closure_hashes = snapshot["source_hashes"]
assert len(closure_hashes) == 104 and len(snapshot["owners"]) == 8
frozen_paths = {path.relative_to(HERE / "snapshot").as_posix()
                for path in (HERE / "snapshot").rglob("*.lean")}
assert frozen_paths == set(closure_hashes)
for path, expected in closure_hashes.items():
    assert sha(HERE / "snapshot" / path) == expected, path
    assert sha(ROOT / path) == expected, path
owner_hashes = {}
for module in snapshot["owners"]:
    path = module.replace(".", "/") + ".lean"
    owner_hashes[path] = closure_hashes[path]
assert owner_hashes == draft["reviewed_owner_source_hashes"]

support = json.loads(PREVIOUS_SUPPORT.read_text())
for record in support["sources"]:
    path = Path(record["path"])
    assert sha(path) == record["whole_file_sha256"]
    lines = path.read_text().splitlines()
    for excerpt in record["excerpts"]:
        assert "\n".join(lines[excerpt["start_line"]-1:excerpt["end_line"]]) + "\n" == excerpt["source"]
support.update(edition="final3", status="PINNED_IMPLEMENTATION_SOURCE_VERIFIED",
               copied_from=str(PREVIOUS_SUPPORT.relative_to(ROOT)),
               copied_from_sha256=sha(PREVIOUS_SUPPORT))

SIMPROC_ROWS = {216, 219, 483, 486}
SIMPROC_ID = {"home": "Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core", "kind": "def",
              "name": "reduceIte", "private": False, "user_name": "reduceIte"}
OPEN_ROWS = {2, 4, 5, 6, 114, 115, 130, 131, 133, 134, 343, 424, 427, 455, 539}
assert {i for i, row in enumerate(native["items"], 1) if row["foreign_definitions"]} == SIMPROC_ROWS
assert {i for i, row in enumerate(native["items"], 1)
        if row["resolution"] in {"UNRESOLVED", "AMBIGUOUS"}} == OPEN_ROWS
assert all(row["resolution"] != "AMBIGUOUS" for row in native["items"])


def named_constant(name):
    result = [candidate for candidate in native["native_candidates"] if candidate["name"] == name]
    assert len(result) == 1, (name, result)
    return result[0]


rows = []
for index, (source, scanned, manual) in enumerate(zip(plan["items"], native["items"], draft["rows"]), 1):
    assert manual["row_id"] == index and manual["head"] == source["head"]
    previous_row = previous["rows"][manual["previous_review_row_id"]-1]
    assert (previous_row["path"], previous_row["declaration"], previous_row["head"], previous_row["item"]) == (
        source["path"], source["declaration"], source["head"], source["item"])
    cls = manual["draft_class"]
    row = {**source, "row_id": index, "status": "REVIEWED", "source_review_class": cls,
           "source_scope_reason": manual["reason"], "native_resolution": scanned["resolution"],
           "native_candidates": scanned["candidates"],
           "native_foreign_definition_candidates": scanned["foreign_definitions"],
           "foreign_definition_body_read": False,
           "previous_review_row_id": manual["previous_review_row_id"]}
    for key in ("lexical_correction", "changed_block_inspection", "changed_occurrence_inspection"):
        if key in manual:
            row[key] = manual[key]
    if cls == "LOCAL_PROOF_EQUATION":
        assert scanned["resolution"] in {"UNRESOLVED", "LOCAL_BINDER_OR_MEMBER"}
        assert not scanned["candidates"]
        selected = None
        disposition = "LOCAL_EQUATION_PROOF_CONFIRMED"
        reason = "The individually recorded source binder is a proof of equality used as a rewrite, not a foreign definition body. Its actual obtain/cases/set/argument binding resolves the lexical name."
    elif cls == "LOCAL_LET_BODY":
        assert scanned["resolution"] == "LOCAL_BINDER_OR_MEMBER" and not scanned["candidates"]
        selected = None
        disposition = "LOCAL_LET_BODY_CONFIRMED"
        reason = "Only the individually recorded proof-local width, u, or w let is expanded. In collisionPost_split the revised list proves the natural-number hwidth equality before whole-list congruence."
    elif cls == "INLINE_EQUATION_PROOF":
        assert index == 114 and scanned["resolution"] == "UNRESOLVED" and not scanned["candidates"]
        selected = None
        disposition = "INLINE_TYPED_EQUATION_PROOF_CONFIRMED"
        reason = "show is term syntax; the equality is supplied by local public-host contract (hs z).2. Definition names in the equality's type are not body-unfold requests."
    elif cls == "BUILTIN_SIMPLIFIER_CONTROL":
        assert index in SIMPROC_ROWS and scanned["candidates"] == [SIMPROC_ID]
        assert scanned["foreign_definitions"] == [SIMPROC_ID] and source["item"] == "↓reduceIte"
        selected = SIMPROC_ID
        disposition = "METAPROGRAM_SIMPROC_ENTRY_CONFIRMED"
        reason = previous_row["disposition_reason"]
        row["supporting_source_evidence"] = str(SUPPORT_PATH.relative_to(ROOT))
    elif cls == "PUBLISHED_THEOREM_DOT_NOTATION":
        assert scanned["resolution"] == "LOCAL_BINDER_OR_MEMBER" and source["head"] == "hw.dlW_eq"
        selected = named_constant(manual["expected_symbol"])
        assert selected["name"] == "TCSlib.Cryptography.Candidates.WellFormedIndex.dlW_eq"
        assert selected["kind"] == "theorem" and selected["home"] == manual["expected_home"]
        disposition = "PUBLISHED_DOT_NOTATION_THEOREM_CONFIRMED"
        reason = "Source hw has type WellFormedIndex n i; dot notation applies its public width theorem. The exact theorem kind/home is confirmed in the fresh native table, including remapped row 568."
    elif cls == "SAME_FILE_DEFINITION":
        assert scanned["resolution"] == "RESOLVED" and len(scanned["candidates"]) == 1
        selected = scanned["candidates"][0]
        assert (selected["name"], selected["kind"], selected["home"]) == (
            manual["expected_symbol"], "def", source["module"])
        assert source["declaration_status"] == "SAME" and not scanned["foreign_definitions"]
        disposition = "SAME_FILE_DEFINITION_CONFIRMED"
        reason = "The exact fresh native definition belongs to this occurrence's own file and appears in an unchanged declaration. This preserved internal body read is not a foreign-file read."
    elif cls in {"CORE_MATHLIB_EQUATION_CANDIDATE", "TCSLIB_PUBLIC_READER_CANDIDATE"}:
        if scanned["resolution"] == "LOCAL_BINDER_OR_MEMBER":
            assert index in {153, 197, 488} and source["head"].startswith("ZMod.")
            selected = named_constant(manual["expected_symbol"])
        else:
            assert scanned["resolution"] == "RESOLVED" and len(scanned["candidates"]) == 1
            selected = scanned["candidates"][0]
        assert (selected["name"], selected["kind"], selected["home"]) == (
            manual["expected_symbol"], "theorem", manual["expected_home"])
        assert not scanned["foreign_definitions"]
        disposition = "NAMED_EQUATION_THEOREM_CONFIRMED"
        reason = "The exact fresh native name/kind/home confirms the individually recorded published equation or contract theorem; this is not the body of a related Core, Mathlib, or TCSlib definition."
    else:
        raise RuntimeError((index, cls))
    row.update(selected_constant=selected, final_native_disposition=disposition, disposition_reason=reason)
    assert not any(word in disposition for word in ("PENDING", "NOT_YET", "UNRESOLVED"))
    rows.append(row)

assert len(rows) == 595 and not any(row["foreign_definition_body_read"] for row in rows)
review = {
    "status": "COMPLETE", "side": "final", "edition": "final3", "reviewed_all_rows": True,
    "row_count": len(rows), "pending_rows": 0, "new_foreign_definition_hits": 0,
    "foreign_definition_body_hits": 0, "native_foreign_definition_candidate_items": 4,
    "native_open_inventory_items_reviewed": 15,
    "proof_commit": draft["proof_commit"],
    "plan": str(PLAN_PATH.relative_to(ROOT)), "plan_sha256": sha(PLAN_PATH),
    "native_scan": str(NATIVE_PATH.relative_to(ROOT)), "native_scan_sha256": sha(NATIVE_PATH),
    "native_log": native["native_log"], "native_log_sha256": native["native_log_sha256"],
    "native_probe_source": plan["module"] + ".lean", "native_probe_source_sha256": plan["source_sha256"],
    "source_snapshot": str(SNAPSHOT_PATH.relative_to(ROOT)), "source_snapshot_sha256": sha(SNAPSHOT_PATH),
    "entire_snapshot_verified": True, "snapshot_module_count": 104,
    "reviewed_import_closure_source_hashes": closure_hashes,
    "reviewed_owner_source_hashes": owner_hashes,
    "draft": str(DRAFT_PATH.relative_to(ROOT)), "draft_sha256": sha(DRAFT_PATH),
    "supporting_simproc_source_evidence": str(SUPPORT_PATH.relative_to(ROOT)),
    "repaired_declarations_inspected": draft["changed_declarations"],
    "occurrence_reorder": [{"previous": row["previous_review_row_id"], "current": row["row_id"], "head": row["head"]}
                           for row in rows if row["previous_review_row_id"] != row["row_id"]],
    "review_method": "All 595 source occurrences were individually rebound by path/declaration/head/item and occurrence order, then checked against the fresh native table. All three repaired declarations were read in full, and moved reader items are explicitly remapped. Every actual def candidate, lexical open item, false ZMod local, and theorem dot-notation occurrence has a specific completed disposition. Entire 104-module frozen/current closure and all eight owner source hashes are verified. Four registered meta simproc entries remain raw foreign-definition candidates; zero request an object-level foreign definition body.",
    "status_counts": dict(Counter(row["declaration_status"] for row in rows)),
    "disposition_counts": dict(Counter(row["final_native_disposition"] for row in rows)),
    "rows": rows,
}
assert sys.argv[1:] == ["--write"]
review_path = HERE / "final-explicit-manual-review.json"
review_path.write_text(json.dumps(review, ensure_ascii=False, indent=2) + "\n")
SUPPORT_PATH.write_text(json.dumps(support, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": "COMPLETE", "row_count": len(rows), "closure_modules_verified": 104,
                  "owner_sources_verified": 8, "raw_foreign_candidates": 4, "body_readings": 0,
                  "review_sha256": sha(review_path), "support_sha256": sha(SUPPORT_PATH),
                  "disposition_counts": review["disposition_counts"]}, ensure_ascii=False, indent=2))
