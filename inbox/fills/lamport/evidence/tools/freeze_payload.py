"""Freeze a complete Lamport payload, verify both manifests, and write its ZIP.

Run with python3 -I only after all writers of this payload have stopped. This
tool refuses an existing snapshot or ZIP. It never invokes Git, Lake or Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import zipfile


def files(root, excluded=()):
    return {p.relative_to(root).as_posix(): p for p in root.rglob('*')
            if p.is_file() and p.relative_to(root).as_posix() not in excluded}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_manifest(root):
    rows = files(root, ('SHA256SUMS',))
    (root / 'SHA256SUMS').write_text(''.join(digest(rows[p]) + '  ' + p + '\n'
                                          for p in sorted(rows)))


def verify(root):
    entries = {}
    for line in (root / 'SHA256SUMS').read_text().splitlines():
        value, path = line.split('  ', 1)
        assert path not in entries and not path.startswith('/') and '..' not in Path(path).parts
        entries[path] = value
    actual = files(root, ('SHA256SUMS',))
    assert set(entries) == set(actual), (set(entries) - set(actual), set(actual) - set(entries))
    for path, value in entries.items():
        assert digest(actual[path]) == value, path
    return len(entries)


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--payload', required=True)
parser.add_argument('--snapshot', required=True)
parser.add_argument('--zip', required=True)
args = parser.parse_args()
payload, snapshot, target_zip = map(lambda p: Path(p).resolve(),
                                    (args.payload, args.snapshot, args.zip))
assert payload.name == snapshot.name == 'lamport'
assert not snapshot.exists() and not target_zip.exists()
write_manifest(payload / 'evidence')
write_manifest(payload)
counts = dict(evidence=verify(payload / 'evidence'), payload=verify(payload))
before = {p: digest(f) for p, f in files(payload).items()}
shutil.copytree(payload, snapshot)
assert before == {p: digest(f) for p, f in files(payload).items()}, 'live writer changed payload'
assert before == {p: digest(f) for p, f in files(snapshot).items()}
assert verify(snapshot / 'evidence') == counts['evidence']
assert verify(snapshot) == counts['payload']
target_zip.parent.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(target_zip, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as archive:
    for path in sorted(before):
        archive.write(snapshot / path, 'lamport/' + path)
with zipfile.ZipFile(target_zip) as archive:
    assert archive.testzip() is None
    assert set(archive.namelist()) == {'lamport/' + p for p in before}
    for path, value in before.items():
        assert hashlib.sha256(archive.read('lamport/' + path)).hexdigest() == value
print(json.dumps(dict(snapshot=str(snapshot), zip=str(target_zip),
                     zip_sha256=digest(target_zip), files=len(before),
                     manifest_entries=counts, exact_path_and_hash_verification=True), indent=2))
