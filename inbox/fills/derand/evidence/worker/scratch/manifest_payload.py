import hashlib
from pathlib import Path
import sys

root = Path(sys.argv[1]).resolve()
assert root.name == 'derand'
def manifest(folder):
    target = folder / 'SHA256SUMS'
    paths = sorted(path for path in folder.rglob('*') if path.is_file() and path != target)
    assert all(not path.is_symlink() for path in paths)
    target.write_text(''.join(hashlib.sha256(path.read_bytes()).hexdigest() + '  ' +
                              path.relative_to(folder).as_posix() + '\n' for path in paths))
    return len(paths)
evidence_count = manifest(root / 'evidence')
total_count = manifest(root)
def check(folder):
    entries = (folder / 'SHA256SUMS').read_text().splitlines()
    expected = set()
    for entry in entries:
        digest, name = entry.split('  ', 1)
        path = folder / name
        assert path.is_relative_to(folder) and path.is_file(), name
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, name
        expected.add(name)
    actual = {path.relative_to(folder).as_posix() for path in folder.rglob('*')
              if path.is_file() and path != folder / 'SHA256SUMS'}
    assert expected == actual, (expected - actual, actual - expected)
check(root / 'evidence')
check(root)
print(f'MANIFEST EXACT-SET PASS: evidence={evidence_count} files; payload={total_count} files')
