"""Recheck immutable evidence, exact source pins, and complete snapshot isolation."""
from pathlib import Path
import hashlib
import json
import datetime

OUT = Path(__file__).resolve().parent
context = json.loads((OUT / "context.json").read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root):
    result = {}
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            result[path.relative_to(root).as_posix()] = dict(kind="symlink", target=str(path.readlink()))
        elif path.is_file():
            result[path.relative_to(root).as_posix()] = dict(kind="file", bytes=path.stat().st_size, sha256=sha(path))
    return result


before = json.loads((OUT / "snapshot-inventory.json").read_text())
snapshot = inventory(Path(context["snapshot"]))
overlay = inventory(Path(context["overlay"]))
assert before == snapshot, "Shared baseline snapshot changed"
target_outputs = {str(Path(path).with_suffix(".olean")) for path in context["compile_order"]}
assert set(overlay) == set(before), "Complete overlay file population changed"
changed = sorted(n for n in overlay if overlay[n] != before[n])
assert set(changed) == target_outputs, changed
source_rows = []
for rel, expected in context["source_pins"].items():
    actual = Path(context["worktree"]) / rel
    archived = OUT / ("SAT-final.lean.txt" if rel.endswith("/SAT.lean") else "Hardness-final.lean.txt")
    assert sha(actual) == sha(archived) == expected
    source_rows.append(dict(path=rel, sha256=expected, actual_equals_archive=True))

pins = {
    "round3-closure-repairs": "76a800243f6c976e5cd140585667502c03f7459e10476bfdfcfcda5968053bdd",
    "round3-extra-repairs": "e2f2d9120e3bc26d90f7850c4f113ef4bd7061405d8161f2fa8ce5f2d35846dd",
    "round3-prefix-repair": "3cfb13406484446aa4f5564e98e30d303bff1718a6edc7d0fdab598cec13b8f0",
}
prior = []
for folder, expected in pins.items():
    root = OUT.parent / folder
    manifest = root / "MANIFEST.json"
    assert sha(manifest) == expected
    rows = json.loads(manifest.read_text())["files"]
    for row in rows:
        path = root / row["path"]
        assert path.stat().st_size == row["bytes"] and sha(path) == row["sha256"], (folder, row["path"])
    control = json.loads((root / "control-check.json").read_text())
    assert control["all_exact_multiplicities_match"]
    prior.append(dict(folder=folder, manifest_sha256=expected,
                      files_reverified=len(rows), controls=control,
                      scope="Separate prior proof-section seals/controls, not a new integrated seal or a seal of legacy source"))

receipt = dict(
    at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    baseline_entries=len(before), shared_snapshot_unchanged=True,
    overlay_entries=len(overlay), complete_population_preserved=True,
    only_compiled_target_outputs_differ=changed,
    changed_outputs={n: dict(before=before[n], after=overlay[n]) for n in changed},
    unchanged_non_target_entries=len(before)-len(changed),
    sources=source_rows, prior_evidence=prior,
    context_limit="Execution began at detached478 with these exact uncommitted bytes; subsequent root commits do not relabel the execution pin. MSG4 pre-#230 dependency context only.",
    no_source_edits=True, no_shared_snapshot_writes=True,
)
(OUT / "final-artifact-verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
(OUT / "overlay-final-inventory.json").write_text(json.dumps(overlay, indent=2, sort_keys=True) + "\n")
artifacts = []
for owner in (OUT / "original9-owners.txt").read_text().splitlines():
    rel = owner.replace(".", "/") + ".olean"
    artifacts.append(dict(owner=owner, path=rel, baseline=before[rel], metadata_input=overlay[rel],
                          origin="Compiled exact final source in this task" if before[rel] != overlay[rel]
                          else "Inherited complete MSG4 compiled artifact; not current post-#230 source"))
(OUT / "metadata-owner-artifacts.json").write_text(json.dumps(artifacts, indent=2) + "\n")
print(json.dumps({k: receipt[k] for k in ["baseline_entries", "shared_snapshot_unchanged", "overlay_entries", "only_compiled_target_outputs_differ", "unchanged_non_target_entries"]}, indent=2))
