"""Independent read-only Rule10 provenance review; no Lean or root mutations."""
from pathlib import Path
import collections
import datetime
import hashlib
import json
import re
import subprocess

root = Path("/Users/seyoonr/.codex/worktrees/seq-zk-proof/tcslib-exchange")
out = Path(__file__).resolve().parent
FINAL = "d842dc8f681f6b89499129f5b64a50d0e4587935"
inputs = {}
def raw(rel):
    data = (root / rel).read_bytes()
    inputs[str(rel)] = hashlib.sha256(data).hexdigest()
    return data
def j(rel):
    return json.loads(raw(rel))
def lines(rel):
    return [json.loads(x) for x in raw(rel).decode().splitlines() if x.strip()]
def key(r):
    return (r["owner"], r["variant"], r["eval"])
def digest(rel):
    return hashlib.sha256(raw(rel)).hexdigest()
def git(*args):
    return subprocess.check_output(["git", *args], cwd=root)
assert git("rev-parse", "HEAD").decode().strip() == FINAL
plans = {phase: j("evidence/rule10/" + phase + "/complete-matrix-plan.json")
         for phase in ["final", "final-repair"]}
for plan in plans.values():
    assert len(plan) == 164 and len({key(r) for r in plan}) == 164
    assert len({r["owner"] for r in plan}) == 41
old = {key(r): r for r in plans["final"]}
new = {key(r): r for r in plans["final-repair"]}
corr = j("evidence/rule10/final-repair/unchanged-cell-correspondence.json")
assert len(corr) == 140
fields = ["source_sha256", "probe_sha256", "rows", "term_excluded", "stored_constants",
          "closure_modules"]
for row in corr:
    k = key(row)
    a, b = j(old[k]["record"]), j(new[k]["record"])
    assert all(a[f] == b[f] for f in fields), k
    assert digest(Path(old[k]["record"]).with_suffix(".lean.txt")) == a["probe_sha256"]
    assert digest(Path(new[k]["record"]).with_suffix(".lean.txt")) == b["probe_sha256"]
affected = j("evidence/rule10/final-repair/affected-owners.json")
assert affected["new"] == FINAL and len(affected["owners"]) == 6
changed = git("diff", "--name-only", affected["old"], FINAL, "--", "TCSlib").decode().splitlines()
assert changed == affected["changed"]
closures = {}
for line in raw("evidence/logs/final-repair-axioms/final-repair-collector.log").decode().splitlines():
    if line.startswith("CLOSURE "):
        row = json.loads(line[8:]); closures[row["module"]] = row["closure"]
changed_mods = {p[:-5].replace("/", ".") for p in changed}
computed = {m for m in closures if m in {r["owner"] for r in plans["final-repair"]}
            and changed_mods.intersection(set(closures[m]) | {m})}
assert computed == set(affected["owners"])
reuse = j("evidence/rule10/final/reuse-provenance.json")
assert len(reuse) == 20
reuse = {key(r["final"]): r for r in reuse}
for k, row in reuse.items():
    assert row["pins_equal"] and row["exact_request_rows_equal"]
    expected = {m.replace(".", "/") + ".lean" for m in closures[k[0]] + [k[0]]}
    assert set(row["source_closure_sha256"]) == expected
    for path, sha in row["source_closure_sha256"].items():
        assert digest(path) == sha
fresh, repaired = {}, {}
for stem, target in [("final", fresh), ("repaired", repaired)]:
    for i in range(1, 4):
        rel = "evidence/logs/" + stem + "-seals-stream-" + str(i) + "/attributed-results.jsonl"
        for r in lines(rel): target[key(r)] = (r, Path(rel).parent)
selected, pending = [], []
for k, finplan in new.items():
    if k[0] in computed:
        item = repaired.get(k); origin = "repair"
    elif k in reuse:
        row = reuse[k]; log = Path(row["retained_log"])
        item = (j(log.with_suffix(".attribution.json")), log.parent); origin = "CP1"
    else:
        item = fresh.get(k); origin = "rev5"
    if item is None:
        pending.append(k); continue
    r, folder = item
    record = j(r["record"]); final = j(finplan["record"])
    log = folder / (r["label"] + ".log"); guard = j(log.with_suffix(".guards.json"))
    assert record["rows"] == final["rows"]
    assert record["source_sha256"] == final["source_sha256"]
    assert guard["native_identity_install_mask_eof_complete"]
    assert guard["request_count"] == final["requested"]
    assert digest(log) == guard["raw_log_sha256"]
    assert digest(r["record"]) == guard["record_sha256"]
    assert digest(Path(r["record"]).with_suffix(".lean.txt")) == record["probe_sha256"]
    count = len(re.findall(r"^\S+\.lean:\d+:\d+: error[:(]", raw(log).decode(), re.M))
    assert count == len(r["errors"]) == guard["proof_error_diagnostics"]
    expected = 10 if k[0].endswith(".Defs") else 0
    assert count == expected and r["exit"] == (1 if expected else 0)
    selected.append({"cell": k, "origin": origin, "raw_log": str(log),
                     "errors": count, "failing_declarations": r["failing_declarations"]})
# Compare the preserved author-facade failures with the actual issue-base cells.
base_defs = {}
for r in lines("evidence/logs/rule10-base-seals/attributed-results.jsonl"):
    rec = j(r["record"])
    if rec["module"].endswith(".Defs"):
        variant = "coe" if "/coe/" in r["record"] else "strict"
        letter = "A" if "/seal-A/" in r["record"] else "B"
        base_defs[(variant, letter)] = r
for r in selected:
    owner, variant, letter = r["cell"]
    if owner.endswith(".Defs"):
        base = base_defs[(variant, letter)]
        assert len(base["errors"]) == r["errors"]
        assert base["failing_declarations"] == r["failing_declarations"]
# Validate all five paired controls directly, including native row identity.
controls = lines("evidence/logs/checkpoint2-controls/control-results.jsonl")
assert len(controls) == 10
for r in controls:
    source = "evidence/rule10/checkpoint2/coe/sources/" + r["module"].split("/")[-1] + ".lean"
    assert digest(source) == r["source_sha256"]
    errors = list(re.finditer(r"^\S+\.lean:(\d+):(\d+): error[:(]", raw(r["raw_log"]).decode(), re.M))
    assert len(errors) == len(r["errors"]) == (1 if r["sealed"] else 0)
    assert r["exit"] == (1 if r["sealed"] else 0) and r["expectation_passed"]
    if r["sealed"]:
        assert int(errors[0][1]) == r["negative_start_line"]
        assert r["expected_error_declaration"] == "HashSignSensitivity.negative"
        g = j(Path(r["raw_log"]).with_suffix(".guards.json"))
        assert g["native_identity_install_mask_eof_complete"] and g["request_count"] == 1
        assert digest(r["raw_log"]) == g["raw_log_sha256"]
        assert digest(g["record"]) == g["record_sha256"]
        native = j(g["record"])["rows"]
        final = j("evidence/rule10/final-repair/coe/seal-" + r["variant"] + "/" + r["request_record"] + ".json")["rows"]
        assert len(native) == 1 and native[0] in final and native[0]["spelling"] == r["target"]
control_prov = j("evidence/rule10/final-repair/control-reuse-provenance.json")
for r in control_prov["records"]:
    assert r["pins_equal"]
    for mod, sha in r["unchanged_definition_home_closure_sha256"].items():
        assert digest(mod.replace(".", "/") + ".lean") == sha
for pin in ["lake-manifest.json", "lean-toolchain"]:
    assert git("show", control_prov["old_revision"] + ":" + pin) == git("show", FINAL + ":" + pin)
# Instrumenter versions and notation boundaries are explicitly represented.
for variant in ["coe", "strict"]:
    for letter in ["A", "B"]:
        m = j("evidence/rule10/final-repair/" + variant + "/seal-" + letter + "/manifest.json")
        assert ("Complexity.PolyExpr.eval" in m["notation_exclusions"]) == (letter == "A")
        assert bool(m["projection_coercions_excluded"]) == (variant == "coe")
        cp2 = j("evidence/rule10/checkpoint2/coe/seal-" + letter + "/manifest.json")
        assert m["tools_sha256"] == cp2["tools_sha256"]
explicit = j("evidence/rule10/final-repair/explicit/explicit-final.json")["summary"]
assert explicit["foreign_items"] == 0
summary = {"read_only": True, "no_Lean_Lake_or_root_mutations": True,
           "review_time_UTC": datetime.datetime.now(datetime.timezone.utc).isoformat(),
           "final_source_revision": FINAL, "final_cells_planned": 164,
           "unchanged_metadata_cells_verified": 140,
           "CP1_full_current_source_closure_hashes_verified": 20,
           "exact_changed_owner_dependency_frontier": sorted(computed),
           "selected_cells_at_snapshot": len(selected), "pending_live_cells": pending,
           "origins_at_snapshot": dict(collections.Counter(r["origin"] for r in selected)),
           "repair_results_passed": sum(r["origin"] == "repair" for r in selected),
           "inherited_Defs_cells_match_issue_base": len(base_defs),
           "paired_controls_verified": 10, "explicit_scan_summary": explicit}
(out / "independent-checks.json").write_text(json.dumps(summary, indent=2) + "\n")
(out / "input-hashes.json").write_text(json.dumps(inputs, indent=2) + "\n")
(out / "selected-at-review.json").write_text(json.dumps(selected, indent=2) + "\n")
print(json.dumps(summary, indent=2))
