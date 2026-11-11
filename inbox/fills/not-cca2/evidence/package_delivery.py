"""Assemble exact committed source, verify patches with a separate index, and zip."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

base = '4a09f3993eb9344fc5714610e41ab141a0144db8'
root = Path('/workspace/scratch/2ed4170fb4ae')
repo = root / 'fill-repo'
payload = root / 'not-cca2'
files = ['TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean',
         'TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean']

def git(*args, env=None):
    return subprocess.check_output(['git', *args], cwd=repo, env=env)

head = git('rev-parse', 'HEAD').decode().strip()
changed = git('diff', '--name-only', base, head).decode().splitlines()
assert sorted(changed) == sorted(files), changed
assert not git('status', '--porcelain'), 'Working tree must match delivery commit'
for file in files:
    path = payload / 'src' / file
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(git('show', head + ':' + file))
inputs = payload / 'evidence' / 'inputs'
inputs.mkdir(exist_ok=True)
for file in (root / 'pack').iterdir():
    if file.is_file():
        shutil.copyfile(file, inputs / file.name)

index = root / 'tmp' / ('verify-' + sys.argv[1] + '.index')
env = {**os.environ, 'GIT_INDEX_FILE': str(index), 'TMPDIR': str(root / 'tmp')}
git('read-tree', base, env=env)
patches = sorted((payload / 'patches').glob('*.patch'))
assert patches
for patch in patches:
    git('apply', '--cached', str(patch), env=env)
checks = []
for file in files:
    actual = git('show', ':' + file, env=env)
    expected = (payload / 'src' / file).read_bytes()
    assert actual == expected, file
    checks.append(dict(path=file, sha256=hashlib.sha256(expected).hexdigest(),
                       bytes=len(expected), lines=expected.count(b'\n')))
provenance = dict(label=sys.argv[1], base=base, head=head, changed_files=changed,
                  patch_replay='PASS: separate index initialized at exact issue base',
                  push_performed=False, source=checks)
(payload / 'evidence' / 'delivery.json').write_text(json.dumps(provenance, indent=2) + '\n')
manifest = payload / 'SHA256SUMS'
entries = [p for p in payload.rglob('*') if p.is_file() and p != manifest]
manifest.write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' +
                            p.relative_to(payload).as_posix() + '\n' for p in sorted(entries)))
output = root / ('not-cca2-' + sys.argv[1] + '.zip')
with zipfile.ZipFile(output, 'w', zipfile.ZIP_DEFLATED) as archive:
    for path in sorted(payload.rglob('*')):
        if path.is_file():
            archive.write(path, Path('not-cca2') / path.relative_to(payload))
with zipfile.ZipFile(output) as archive:
    assert archive.testzip() is None
print(json.dumps(dict(path=str(output), bytes=output.stat().st_size,
                     sha256=hashlib.sha256(output.read_bytes()).hexdigest(),
                     head=head, patch_replay='PASS')))
