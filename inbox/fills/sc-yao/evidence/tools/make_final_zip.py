#!/usr/bin/env python3
"""Archive the exact sealed payload under sc-yao/ and verify every archived byte hash."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

p = argparse.ArgumentParser()
p.add_argument('payload')
p.add_argument('archive')
p.add_argument('--receipt', required=True)
a = p.parse_args()
payload, archive = Path(a.payload), Path(a.archive)
assert not archive.exists()
files = sorted(q for q in payload.rglob('*') if q.is_file())
assert (payload / 'SHA256SUMS').is_file()
expected = {'sc-yao/' + q.relative_to(payload).as_posix(): q for q in files}
assert all('..' not in Path(n).parts and not n.startswith('./') for n in expected)
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as z:
    for name, source in expected.items():
        z.write(source, name)
inventory = []
with zipfile.ZipFile(archive) as z:
    assert len(z.namelist()) == len(expected) and set(z.namelist()) == set(expected)
    assert {n.split('/')[0] for n in z.namelist()} == {'sc-yao'}
    for name, source in expected.items():
        digest = hashlib.sha256()
        with z.open(name) as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b''):
                digest.update(chunk)
        actual = digest.hexdigest()
        assert actual == hashlib.sha256(source.read_bytes()).hexdigest(), name
        inventory.append(dict(path=name, bytes=source.stat().st_size, sha256=actual))
digest = hashlib.sha256()
with archive.open('rb') as stream:
    for chunk in iter(lambda: stream.read(1024 * 1024), b''):
        digest.update(chunk)
receipt = dict(archive=str(archive), sha256=digest.hexdigest(), bytes=archive.stat().st_size,
    files=len(inventory), root='sc-yao/', exact_payload_paths=True,
    all_entry_hashes_verified=True, inventory=inventory)
Path(a.receipt).write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k: v for k, v in receipt.items() if k != 'inventory'}))
