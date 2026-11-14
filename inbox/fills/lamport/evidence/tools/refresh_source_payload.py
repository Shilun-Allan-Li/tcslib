"""Export the frozen local source commit and verify its full patch series.

Run with python3 -I. The reproduction directory is a source-only archive, with
no Lake configuration, packages or oleans; this tool never invokes Lean.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

BASE = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
OWNED = 'TCSlib/Cryptography/Authentication/Signatures/Lamport.lean'
FACADE = 'TCSlib/Cryptography/Authentication.lean'
HELPERS = OWNED[:-5] + '/'


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', required=True)
parser.add_argument('--payload', required=True)
parser.add_argument('--commit', required=True)
parser.add_argument('--phase', required=True)
args = parser.parse_args()
root, payload = Path(args.root).resolve(), Path(args.payload).resolve()
head = git(root, 'rev-parse', args.commit).decode().strip()
paths = git(root, 'diff', '--name-only', BASE, head).decode().splitlines()
assert paths and all(p in (OWNED, FACADE) or p.startswith(HELPERS) for p in paths), paths
src, patches = payload / 'src', payload / 'patches'
src.mkdir(exist_ok=True)
patches.mkdir(exist_ok=True)
for path in src.rglob('*'):
    if path.is_file():
        path.unlink()
for path in patches.glob('*.patch'):
    path.unlink()
records = []
for path in paths:
    raw = git(root, 'show', head + ':' + path)
    target = src / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(raw)
    assert len(raw.splitlines()) < 1000, path
    records.append(dict(path=path, sha256=hashlib.sha256(raw).hexdigest(),
                        lines=len(raw.splitlines())))
patch_names = git(root, 'format-patch', '-o', str(patches), BASE + '..' + head).decode().splitlines()
reproduce = payload.parent.parent / ('reproduce-' + args.phase)
reproduce.mkdir(exist_ok=False)
base_archive = git(root, 'archive', BASE, 'TCSlib')
with tarfile.open(fileobj=io.BytesIO(base_archive)) as archive:
    archive.extractall(reproduce, filter='data')
checks = []
for name in patch_names:
    for mode in ('--check', '--apply'):
        argv = ['git', 'apply'] + (['--check'] if mode == '--check' else []) + [name]
        result = subprocess.run(argv, cwd=reproduce, capture_output=True, text=True)
        checks.append(dict(command=argv, status=result.returncode,
                           stdout=result.stdout, stderr=result.stderr))
        assert result.returncode == 0, checks[-1]
for row in records:
    assert (reproduce / row['path']).read_bytes() == (src / row['path']).read_bytes(), row
result = dict(base=BASE, head=head, reproduction=str(reproduce),
              source_records=records, patches=patch_names, checks=checks,
              exact_reproduction=True, compiler_run=False)
output = payload / 'evidence/logs' / ('source-payload-' + args.phase + '.json')
assert not output.exists(), output
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(head=head, files=len(records), patches=len(patch_names),
                     all_below_1000=True, exact_reproduction=True), indent=2))
