"""Package the checked selected-step wrapper separately from immutable b5."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile

summary = json.loads(Path('evidence/subagents/b6/final-summary.json').read_text())
dest = Path('/private/tmp/sc-yao-b-handoff-v6')
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
shutil.copytree('evidence/subagents/b6', dest / 'evidence/subagents/b6')
(dest / 'README.md').write_text('''# SelectedStep final handoff

SelectedStep.reconstruct proves both neighboring actual hybrid sample endpoints from the
same before-stage Plan.advice, with identical slot offsets/lengths and side-specific
messages. It takes an actual argument p; absent-argument branches are c's GateStepCases.
Fan-in, consistent wire values, canonical rows, occurrence capacity and outs_sink suffice.
Plaintext-label and output-key separation are derived internally. Actual key values may
collide and key width may be zero. No adversary, runtime premise, distribution law, or
global nonempty gate/vertex assumption occurs in this pointwise contract.

All four whole-file A/B strict/coe seals pass with maxErrors=0, and the exact final source
passes its normal check. All stored declarations have empty sorry closures and only the
standard axioms listed in evidence/subagents/b6/final-summary.json. The style lint is clean;
source width is at most 100 and size 217 lines. The evidence REUSE.md records each reader and
inline proof shape. The source is unchanged from immutable normal06 API, hash
6aed6ba596997e39eae312b9ee5842ef57184283000cff80d8487d37cec4b4d2.

Dependencies are the immutable b5-final nine-module handoff plus c's verified
SelectedFields and shared GateHybrids/GateHybridMessage closure. Only the new SelectedStep
source and its exact-source matching olean are contributed here. No commits, frozen edits,
parent-owned source changes or delivery pushes were made. Parent owns the probability and
negligibility assembly, target integration, final sweep and delivery.
''')
records = [hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + str(p.relative_to(dest))
           for p in sorted(dest.rglob('*')) if p.is_file()]
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
for p in sorted(dest.rglob('*'), reverse=True):
    p.chmod(0o555 if p.is_dir() else 0o444)
dest.chmod(0o555)
archive.chmod(0o444)
Path(str(archive) + '-SHA256SUMS').chmod(0o444)
print('HANDOFF', str(dest))
print('FILES', len(records) + 1)
print('ARCHIVE', str(archive))
print('SHA256', archive_hash)
