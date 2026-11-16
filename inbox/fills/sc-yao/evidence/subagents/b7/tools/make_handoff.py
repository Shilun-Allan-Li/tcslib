"""Package the two checked uniform selected-step security modules and all evidence."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile

summary = json.loads(Path('evidence/subagents/b7/final-summary.json').read_text())
dest = Path('/private/tmp/sc-yao-b-handoff-v7')
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
shutil.copytree('evidence/subagents/b7', dest / 'evidence/subagents/b7')
(dest / 'README.md').write_text('''# Uniform selected-neighbor security handoff

SelectedStepChoices supplies the complete fixed finite choice family, with None for empty
input/gate types, all slice-fit and advice bounds, and exact reconstruction endpoints.
SelectedStepSecurity.selected_negligible proves one nonnegative negligible bound uniformly
in parameter, input, actual gate and argument for the actual addressed uniform tape sampler.
It consumes actual SliceMultiMessageSecure B1, not an assumed neighboring-step bound.
No extra sampler identity, PTC leaf, nonempty gate/vertex, or permutation-uniformity premise
is left beyond the explicit uniform leaf and four addressed seed readers in its header.

Both exact-source final normals and all eight A/B strict/coe whole-file seals pass. All
stored constants have empty sorry closures and only the standard axioms listed in
final-summary.json. Style has zero findings, widths are at most100 and sizes316/229lines.
Source/API hashes and complete raw logs, seal sources, dependency signatures/axioms/closures,
reuse disclosures, diagnostics and replaced-parent dependency history are included.

These two sources and matching oleans are unchanged from the stable API shared with root/a.
The existing immutable b5/v6 sources remain untouched. Root owns SelectedLaw/CoordinateSwap;
a owns GateHybridChain and GateHybridSecurity/concrete integration. No child commits,
frozen edits or delivery pushes were made. Parent owns final sweep, commits and delivery.
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
