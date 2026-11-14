#!/usr/bin/env python3
"""Materialize all manual native/source dispositions; no Lean/Lake invocation."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
EDITION = ROOT / "evidence/probes/Rule10/final2"
PLAN = EDITION / "final-scan-plan.json"
NATIVE = EDITION / "final-explicit-scan.json"
DRAFT = EDITION / "final-explicit-manual-draft.json"
SNAPSHOT = EDITION / "snapshot.json"
SUPPORT = "evidence/probes/Rule10/final2/explicit-simproc-source-evidence.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


plan = json.loads(PLAN.read_text())
scan = json.loads(NATIVE.read_text())
draft = json.loads(DRAFT.read_text())
snapshot = json.loads(SNAPSHOT.read_text())
assert draft["plan_sha256"] == sha(PLAN)
assert plan["items"] == [{k: v for k, v in row.items()
                          if k not in {"resolution", "candidates", "foreign_definitions"}}
                         for row in scan["items"]]
assert len(plan["items"]) == len(draft["rows"]) == len(scan["items"]) == 595
assert sha(ROOT / scan["native_log"]) == scan["native_log_sha256"]
source_hashes = {}
for path in {row["path"] for row in plan["items"]}:
    assert sha(ROOT / path) == snapshot["source_hashes"][path]
    assert sha(EDITION / "snapshot" / path) == snapshot["source_hashes"][path]
    source_hashes[path] = snapshot["source_hashes"][path]

# The four actual foreign-def candidate rows were inspected individually.
# Each syntax node is a registered builtin Simproc entry, not a request to
# unfold the object-level body of the native constant.
SIMPROC_NOTES = {
    216: "Algebra.unitCollision_extract, false/true-selector case: after Bool.false_eq_true, reduceIte selects the proved conditional branch; one_mul is a separate equation theorem",
    219: "Algebra.unitCollision_extract, true/false-selector case: reduceIte selects the conditional branch in the goal and collision hypothesis; no definition body is rewritten",
    483: "dlHashEval_expF, false-selector branch: reduceIte simplifies the now-known false conditional before the unit-power value reader applies",
    486: "dlHashEval_expF, true-selector branch: reduceIte simplifies the now-known true conditional before the unit multiplication/value readers apply",
}
SIMPROC_ID = {
    "home": "Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core",
    "kind": "def", "name": "reduceIte", "private": False,
    "user_name": "reduceIte",
}
DOT_NAME = "TCSlib.Cryptography.Candidates.WellFormedIndex.dlW_eq"
FALSE_LOCALS = {153: "ZMod.val_natCast", 197: "ZMod.val_natCast", 488: "ZMod.val_mul"}
OPEN_LOCAL_ROWS = {2, 4, 5, 6, 115, 130, 131, 133, 134, 343, 424, 427, 455, 539}
DOT_ROWS = {398, 437, 446, 457, 477, 480, 491, 494, 540, 573, 580, 588}
assert {i for i, r in enumerate(scan["items"], 1) if r["foreign_definitions"]} == set(SIMPROC_NOTES)
assert {i for i, r in enumerate(scan["items"], 1)
        if r["resolution"] in {"UNRESOLVED", "AMBIGUOUS"}} == OPEN_LOCAL_ROWS | {114}


def native_named(name):
    candidates = [c for c in scan["native_candidates"] if c["name"] == name]
    assert len(candidates) == 1, (name, candidates)
    return candidates[0]


toolchain = Path("/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean")
requests = {
    "Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean": [(10, 25)],
    "Lean/Elab/Tactic/Simp.lean": [(94, 128), (250, 266), (333, 344)],
}
support_sources = []
for relative, ranges in requests.items():
    path = toolchain / relative
    lines = path.read_text().splitlines()
    support_sources.append({
        "path": str(path), "whole_file_sha256": sha(path),
        "excerpts": [{"start_line": lo, "end_line": hi,
                      "source": "\n".join(lines[lo-1:hi]) + "\n"}
                     for lo, hi in ranges],
    })
support = {
    "lean_pin": "4.25.0",
    "purpose": "Disposition of actual native def candidates reduceIte in four explicit simp entries",
    "source_review": "Pinned source registers reduceIte as a builtin_simproc. resolveSimpIdTheorem? returns .simproc for a registered procedure; elabSimpLemma returns .addSimproc, and elabSimpArgs adds it to the procedure set. This bypasses the .expr/elabDeclToUnfoldOrTheorem path. The procedure constructs proofs with ite_cond_eq_true or ite_cond_eq_false.",
    "sources": support_sources,
}

rows = []
for index, (item, native, manual) in enumerate(zip(plan["items"], scan["items"], draft["rows"]), 1):
    assert manual["row_id"] == index and manual["head"] == item["head"]
    cls = manual["draft_class"]
    row = {**item, "row_id": index, "source_review_class": cls,
           "source_scope_reason": manual["reason"],
           "native_resolution": native["resolution"],
           "native_candidates": native["candidates"],
           "native_foreign_definition_candidates": native["foreign_definitions"],
           "status": "REVIEWED", "foreign_definition_body_read": False}
    if "lexical_correction" in manual:
        row["lexical_correction"] = manual["lexical_correction"]
    if cls == "LOCAL_PROOF_EQUATION":
        assert native["resolution"] in {"LOCAL_BINDER_OR_MEMBER", "UNRESOLVED"}
        assert not native["candidates"]
        row.update(final_native_disposition="LOCAL_EQUATION_PROOF_CONFIRMED",
                   selected_constant=None,
                   disposition_reason="The source occurrence rewrites by the individually identified local proof of equality. It does not expand a foreign definition. Its binder provenance takes priority over global same-suffix candidates.")
    elif cls == "LOCAL_LET_BODY":
        assert native["resolution"] == "LOCAL_BINDER_OR_MEMBER" and not native["candidates"]
        row.update(final_native_disposition="LOCAL_LET_BODY_CONFIRMED", selected_constant=None,
                   disposition_reason="This exact occurrence expands only the recorded local let (width, u, or w). Local proof data are not foreign module definitions.")
    elif cls == "INLINE_EQUATION_PROOF":
        assert index == 114 and native["resolution"] == "UNRESOLVED" and not native["candidates"]
        row.update(final_native_disposition="INLINE_TYPED_EQUATION_PROOF_CONFIRMED",
                   selected_constant=None,
                   disposition_reason="show is term syntax. The equality used by rw is supplied by the local public-host contract (hs z).2, rather than by unfolding rejectBlocksL or another definition appearing in its type.")
    elif cls == "BUILTIN_SIMPLIFIER_CONTROL":
        assert index in SIMPROC_NOTES and native["candidates"] == [SIMPROC_ID]
        assert native["foreign_definitions"] == [SIMPROC_ID]
        assert item["item"] == "↓reduceIte"
        row.update(final_native_disposition="METAPROGRAM_SIMPROC_ENTRY_CONFIRMED",
                   selected_constant=SIMPROC_ID,
                   disposition_reason=SIMPROC_NOTES[index] + ". The pinned elaborator recognizes the registered procedure and takes its addSimproc branch, not its declaration-unfold branch. The meta definition is invoked to construct conditional-equation proofs; its body is not unfolded in the object proof.",
                   supporting_source_evidence=SUPPORT)
    elif cls == "PUBLISHED_THEOREM_DOT_NOTATION":
        assert index in DOT_ROWS and native["resolution"] == "LOCAL_BINDER_OR_MEMBER"
        selected = native_named(DOT_NAME)
        assert selected["kind"] == "theorem" and selected["home"] == "TCSlib.Cryptography.Candidates.DiscreteLog"
        row.update(final_native_disposition="PUBLISHED_DOT_NOTATION_THEOREM_CONFIRMED",
                   selected_constant=selected,
                   disposition_reason="The source binder hw has type WellFormedIndex n i. Dot notation selects its exact public dlW_eq theorem, which the native table confirms is a theorem in Candidates.DiscreteLog. No local or generated definition body is unfolded.")
    elif cls == "SAME_FILE_DEFINITION":
        assert native["resolution"] == "RESOLVED" and len(native["candidates"]) == 1
        selected = native["candidates"][0]
        assert selected["kind"] == "def" and selected["home"] == item["module"]
        assert item["declaration_status"] == "SAME" and not native["foreign_definitions"]
        row.update(final_native_disposition="SAME_FILE_DEFINITION_CONFIRMED", selected_constant=selected,
                   disposition_reason="The native constant is a definition from this occurrence's own file. The surrounding declaration is unchanged at the issue base. Rule 10 forbids foreign-file body reads; this is a preserved internal provider/owned-file read.")
    elif cls in {"CORE_MATHLIB_EQUATION_CANDIDATE", "TCSLIB_PUBLIC_READER_CANDIDATE"}:
        if index in FALSE_LOCALS:
            selected = native_named(FALSE_LOCALS[index])
            assert native["resolution"] == "LOCAL_BINDER_OR_MEMBER" and not native["candidates"]
        else:
            assert native["resolution"] == "RESOLVED" and len(native["candidates"]) == 1
            selected = native["candidates"][0]
        assert selected["kind"] == "theorem" and not native["foreign_definitions"]
        row.update(final_native_disposition="NAMED_EQUATION_THEOREM_CONFIRMED", selected_constant=selected,
                   disposition_reason="The exact fully qualified native constant and home recorded here confirm a theorem, not a def. This occurrence consumes its published equation/contract; it does not request the body of a related definition.")
    else:
        raise RuntimeError((index, cls))
    assert not any(word in row["final_native_disposition"] for word in ("PENDING", "NOT_YET", "UNRESOLVED"))
    rows.append(row)

assert len(rows) == 595 and all(row["status"] == "REVIEWED" for row in rows)
assert not any(row["foreign_definition_body_read"] for row in rows)
result = {
    "status": "COMPLETE", "side": "final", "edition": "final2",
    "reviewed_all_rows": True, "row_count": len(rows), "pending_rows": 0,
    "new_foreign_definition_hits": 0, "foreign_definition_body_hits": 0,
    "native_foreign_definition_candidate_items": 4,
    "native_open_inventory_items_reviewed": 15,
    "plan": str(PLAN.relative_to(ROOT)), "plan_sha256": sha(PLAN),
    "native_scan": str(NATIVE.relative_to(ROOT)), "native_scan_sha256": sha(NATIVE),
    "native_log": scan["native_log"], "native_log_sha256": scan["native_log_sha256"],
    "source_snapshot": str(SNAPSHOT.relative_to(ROOT)), "source_snapshot_sha256": sha(SNAPSHOT),
    "reviewed_owner_source_hashes": source_hashes,
    "draft": str(DRAFT.relative_to(ROOT)), "draft_sha256": sha(DRAFT),
    "supporting_simproc_source_evidence": SUPPORT,
    "review_method": "Row-by-row manual source review joined with the native kind/home table. Explicit overrides dispose every local-binding omission, false type-name local, theorem dot-notation item, inline equation proof, and all four actual foreign-def candidates. The four foreign metaprogram definitions are registered simproc entries, not object-level body unfold requests. Every other named global is individually recorded as a native theorem or a same-file definition; unexpected kinds/homes abort materialization.",
    "status_counts": dict(Counter(row["declaration_status"] for row in rows)),
    "disposition_counts": dict(Counter(row["final_native_disposition"] for row in rows)),
    "rows": rows,
}
if sys.argv[1:] == ["--write"]:
    review_path = EDITION / "final-explicit-manual-review.json"
    support_path = ROOT / SUPPORT
    review_path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    support_path.write_text(json.dumps(support, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "row_count": len(rows),
                      "disposition_counts": result["disposition_counts"],
                      "raw_foreign_candidates": 4, "foreign_definition_body_hits": 0,
                      "review_sha256": sha(review_path), "support_sha256": sha(support_path)},
                     ensure_ascii=False, indent=2))
else:
    assert not sys.argv[1:]
    print(json.dumps({"review": result, "supporting_sources": support},
                     ensure_ascii=False, separators=(",", ":")))
