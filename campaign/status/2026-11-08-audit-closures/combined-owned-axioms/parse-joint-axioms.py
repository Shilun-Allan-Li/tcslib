from pathlib import Path
import collections
import datetime
import hashlib
import json

p = Path("/private/tmp/ab34-joint-axioms")
run = json.loads((p / "run.json").read_text())
context = json.loads((p / "context.json").read_text())
expected = json.loads((p / "expected-owned-axioms.json").read_text())
assert run["exit"] == 0 and run["probe_unchanged"] and run["all895_object_hashes_unchanged"]
assert run["source"] == context["intended_combined_source"]
assert run["probe_sha256"] == context["probe_sha256"]
raw = (p / "JointAxioms.out").read_bytes()
assert len(raw) == run["output_bytes"] and hashlib.sha256(raw).hexdigest() == run["output_sha256"]
assert "error:" not in raw.decode()
actual = {}
complete = []
for line in raw.decode().splitlines():
    if "JOINTAX|" in line:
        row = json.loads(line.split("JOINTAX|", 1)[1])
        name = row.pop("name")
        assert name not in actual and row["owner"] in context["owners"]
        assert len(row["axioms"]) == len(set(row["axioms"]))
        row["axioms"] = sorted(row["axioms"])
        actual[name] = row
    elif "COMPLETE|" in line:
        complete.append(line.split("COMPLETE|", 1)[1].strip())
assert complete == [f"{len(actual)}|owners=20"]
assert len(set(context["owners"])) == 20
standard = {"propext", "Quot.sound", "Classical.choice"}
nonstandard = {n: row for n, row in actual.items() if set(row["axioms"]) - standard}
old_nonstandard = {n: row for n, row in expected.items() if set(row["axioms"]) - standard}
assert len(old_nonstandard) == 3 and nonstandard == old_nonstandard
added = {n: actual[n] for n in actual.keys() - expected.keys()}
removed = {n: expected[n] for n in expected.keys() - actual.keys()}
changed = {
    n: {"expected_old_context_comparison": expected[n], "actual_combined": actual[n],
        "fields": [k for k in expected[n] if expected[n][k] != actual[n][k]]}
    for n in actual.keys() & expected.keys() if actual[n] != expected[n]
}
for filename, data in [("actual-owned-axioms.json", actual), ("nonstandard-owned-dependencies.json", nonstandard),
                       ("old-context-comparison-delta.json", dict(added=added, removed=removed, changed=changed))]:
    (p / filename).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
summary = dict(
    utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    result="PASS execution/integrity and no new nonstandard dependencies in20 owners; root dispositions required for any comparison delta",
    source=run["source"], owners=20, constants=len(actual), expected_old_context_constants=len(expected),
    counts_by_owner=dict(sorted(collections.Counter(row["owner"] for row in actual.values()).items())),
    nonstandard_dependency_closures=len(nonstandard), exact_to_three_inherited_WordSize_rows=True,
    comparison_added=len(added), comparison_removed=len(removed), comparison_changed=len(changed),
    changed_fields=dict(collections.Counter(k for row in changed.values() for k in row["fields"])),
    root_comparison_disposition_needed=bool(added or removed or changed),
    all895_objects_unchanged=True,
    limits="All constants in20 selected owners, including private/generated; not all394 modules or all895 objects. No new type/proof-value equality, opacity, source-screen, semantic-absence, global admission-free or debt-retirement claim.",
)
(p / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
