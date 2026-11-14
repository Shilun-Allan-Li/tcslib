#!/usr/bin/env python3
"""Source-reviewed occurrence rebind for final3; no Lean/Lake invocation."""
from collections import Counter, defaultdict, deque
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
OLD = ROOT / "evidence/probes/Rule10/final2"
NEW = ROOT / "evidence/probes/Rule10/final3"
old_plan_path = OLD / "final-scan-plan.json"
new_plan_path = NEW / "final-scan-plan.json"
old_review_path = OLD / "final-explicit-manual-review.json"
old_plan = json.loads(old_plan_path.read_text())
new_plan = json.loads(new_plan_path.read_text())
old_review = json.loads(old_review_path.read_text())
snapshot = json.loads((NEW / "snapshot.json").read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert old_review["status"] == "COMPLETE" and old_review["reviewed_all_rows"]
assert old_review["plan_sha256"] == sha(old_plan_path)
assert len(old_plan["items"]) == len(new_plan["items"]) == len(old_review["rows"]) == 595

# These three complete proof blocks were explicitly inspected in fa33b9b8f.
# Local dimension equality and whole-list congruence replace dependent simpa;
# key-value field readers precede dimension evaluation in both main proofs.
EXPECTED_CHANGED = {
    "TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split",
    "TCSlib.Cryptography.Authentication.dlHash_compresses",
    "TCSlib.Cryptography.Authentication.dlHash_collision_accept_eq",
}
changed = []
for path, declarations in new_plan["declarations"].items():
    before = {decl["name"]: decl for decl in old_plan["declarations"][path]}
    assert {decl["name"] for decl in declarations} == set(before)
    for declaration in declarations:
        if declaration["code_hash"] != before[declaration["name"]]["code_hash"]:
            changed.append({"path": path, "declaration": declaration["name"],
                            "before_code_hash": before[declaration["name"]]["code_hash"],
                            "after_code_hash": declaration["code_hash"]})
assert {row["declaration"] for row in changed} == EXPECTED_CHANGED


def key(row):
    # Occurrence order is retained for repeated identical reader items inside a
    # declaration; line/tactic positions are deliberately not treated as identity.
    return row["path"], row["declaration"], row["head"], row["item"]


available = defaultdict(deque)
for old_item, old_row in zip(old_plan["items"], old_review["rows"]):
    assert old_row["head"] == old_item["head"]
    available[key(old_item)].append((old_item, old_row))

rows = []
for index, item in enumerate(new_plan["items"], 1):
    assert available[key(item)], (index, key(item))
    old_item, previous = available[key(item)].popleft()
    assert previous["declaration_status"] == item["declaration_status"]
    cls = previous["source_review_class"]
    local = cls in {"LOCAL_PROOF_EQUATION", "LOCAL_LET_BODY", "INLINE_EQUATION_PROOF"}
    row = {"row_id": index, "head": item["head"],
           "declaration_status": item["declaration_status"],
           "draft_class": cls, "reason": previous["source_scope_reason"],
           "previous_review_row_id": previous["row_id"],
           "previous_review_disposition": previous["final_native_disposition"],
           "draft_disposition": "SOURCE_SCOPE_REVIEWED" if local else "PENDING_NATIVE_KIND_HOME",
           "final_native_disposition": "NOT_YET_REVIEWED"}
    selected = previous["selected_constant"]
    if selected:
        row.update(expected_kind=selected["kind"], expected_symbol=selected["name"],
                   expected_home=selected["home"])
    else:
        row["expected_kind"] = "local proof term" if cls == "LOCAL_PROOF_EQUATION" else "local let" if cls == "LOCAL_LET_BODY" else "term syntax"
    if "lexical_correction" in previous:
        row["lexical_correction"] = previous["lexical_correction"]
    if item["declaration"] == "TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split":
        row["changed_block_inspection"] = "Read complete revised collisionPost_split: hwidth proves a natural-number dimension equality; congrArg of k ↦ List.ofFn (padFin k raw) transports a whole List Bool; exact published padding reader closes hword. No foreign definition body is used. All remaining proof steps are preserved."
        if index in {360, 361, 362, 363, 364, 365}:
            row["changed_occurrence_inspection"] = "This six-item list now proves only hwidth, not a dependent bit-vector/list equality; its PolyExpr reads are public eval constructor equations."
        if index == 360:
            assert item["head"] == "width"
            row["reason"] = "width: proof-local PolyExpr expanded only in the new natural-number hwidth equality inside collisionPost_split"
        if index == 361:
            assert item["head"] == "u"
            row["reason"] = "u: proof-local unary parameter word expanded only in the new natural-number hwidth equality"
    if item["declaration"] in EXPECTED_CHANGED - {"TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split"}:
        row["changed_block_inspection"] = "Read complete revised proof: the first simp list applies published key/value/field equations, and the second evaluates domain/range dimensions through published equations. The reader multiset is unchanged; staging avoids dependent casts requiring foreign body reduction."
    rows.append(row)
assert not any(available.values())

hashes = {}
for path in {item["path"] for item in new_plan["items"]}:
    assert sha(ROOT / path) == snapshot["source_hashes"][path]
    assert sha(NEW / "snapshot" / path) == snapshot["source_hashes"][path]
    hashes[path] = snapshot["source_hashes"][path]
result = {
    "status": "DRAFT_SOURCE_REVIEW_NATIVE_KIND_HOME_PENDING", "edition": "final3", "side": "final",
    "proof_commit": "fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16",
    "plan": str(new_plan_path.relative_to(ROOT)), "plan_sha256": sha(new_plan_path),
    "source_snapshot": str((NEW / "snapshot.json").relative_to(ROOT)),
    "source_snapshot_sha256": sha(NEW / "snapshot.json"),
    "reviewed_owner_source_hashes": hashes,
    "previous_review": str(old_review_path.relative_to(ROOT)), "previous_review_sha256": sha(old_review_path),
    "review_method": "Exact path/declaration/head/item occurrence matching with previous complete source/native dispositions, plus explicit inspection of all three repaired proof blocks. Repeated identical items use their within-declaration occurrence order. Source hashes and exact changed-declaration set are checked. Native final3 results remain required.",
    "row_count": len(rows), "status_counts": dict(Counter(row["declaration_status"] for row in rows)),
    "draft_class_counts": dict(Counter(row["draft_class"] for row in rows)),
    "changed_declarations": changed, "rows": rows,
}
if sys.argv[1:] == ["--write"]:
    path = NEW / "final-explicit-manual-draft.json"
    path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"row_count": len(rows), "plan_sha256": result["plan_sha256"],
                      "draft_sha256": sha(path), "changed_declarations": changed,
                      "moved_occurrences": [{"old": row["previous_review_row_id"], "new": row["row_id"], "head": row["head"]}
                                            for row in rows if row["row_id"] != row["previous_review_row_id"]]},
                     ensure_ascii=False, indent=2))
else:
    assert not sys.argv[1:]
    print(json.dumps(result, ensure_ascii=False))
