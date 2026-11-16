"""Create an immutable source/artifact/evidence handoff after all checks pass."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import tarfile

summary = json.loads(Path('evidence/subagents/b5/final-summary.json').read_text())
dest = Path('/private/tmp/sc-yao-b-handoff-v5-final')
assert not dest.exists()
dest.mkdir()
for row in summary['modules']:
    rel = Path(row['source'])
    target = dest / 'src' / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(rel, target)
    artifact = rel.with_suffix('.olean')
    target = dest / 'oleans' / artifact
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(Path('.lake/sc-yao-oleans') / artifact, target)
shutil.copytree('evidence/subagents/b5', dest / 'evidence/subagents/b5')
old = Path('/private/tmp/sc-yao-b-handoff-v5-paused/upstream-checked')
if old.is_dir():
    shutil.copytree(old, dest / 'upstream-checked')
(dest / 'README.md').write_text('''# Completed b5 reconstruction handoff

All nine contributed sources and their exact-source matching oleans are included.
All 36 whole-file A/B strict/coe seals pass with maxErrors=0. Nine final source checks
pass sequentially through the shared sc-yao-b wrapper. The all-stored-constant trace has
only propext, Classical.choice and Quot.sound and no nonempty sorry dependency closure.
See evidence/subagents/b5/final-summary.json for exact counts, hashes and raw records.

The exact actual hybrid sample is SelectedTables.sample_reconstruct. The total raw
machine is SliceReconstruction.rebuild_poly (only E2 polynomial-time is required).
SelectedAdviceBounds.sample_advice_budget closes the complete actual view advice bound.
SeedCoordinates/NonceCoordinates supply exact coordinate fill and partial inverses;
root owns SelectedLaw, c owns TapeValues/SelectedFields, and a owns CoordinateSwap.

See evidence/subagents/b5/RECONSTRUCTION.md for formulas, symbolic-label assumptions, overlap/reuse disclosure,
and preserved invocation/environment failures. RESUME.md and paused-summary.json inside
the evidence are historical relocation checkpoints, superseded by final-summary.json.
The upstream-checked SliceReduction source is the immutable earlier checked parent copy,
not an agent-b contribution. No child commits or frozen edits were made.

Remaining task after this handoff: SelectedStep will combine c's stage-label and
unselected-row readers with sample_reconstruct to expose both neighboring selected
substep endpoints using identical before-stage advice. That new module is excluded here;
its initial unverified draft is retained separately in /private/tmp. Parent owns the
probability/negligibility assembly, concrete target integration, final sweep and delivery.
''')
records = []
for path in sorted(dest.rglob('*')):
    if path.is_file():
        records.append(hashlib.sha256(path.read_bytes()).hexdigest() + '  ' +
                       str(path.relative_to(dest)))
(dest / 'SHA256SUMS').write_text('\n'.join(records) + '\n')
for line in records:
    digest, rel = line.split('  ', 1)
    assert hashlib.sha256((dest / rel).read_bytes()).hexdigest() == digest
archive = dest.with_suffix('.tar.gz')
assert not archive.exists()
with tarfile.open(archive, 'w:gz') as output:
    output.add(dest, arcname=dest.name)
archive_hash = hashlib.sha256(archive.read_bytes()).hexdigest()
Path(str(archive) + '-SHA256SUMS').write_text(archive_hash + '  ' + archive.name + '\n')
for path in sorted(dest.rglob('*'), reverse=True):
    path.chmod(0o555 if path.is_dir() else 0o444)
dest.chmod(0o555)
archive.chmod(0o444)
Path(str(archive) + '-SHA256SUMS').chmod(0o444)
print('HANDOFF', str(dest))
print('FILES', len(records) + 1)
print('ARCHIVE', str(archive))
print('SHA256', archive_hash)
