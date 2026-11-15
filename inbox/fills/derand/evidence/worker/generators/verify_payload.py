"""Verify hashes, exact delivered file sets, and optionally the Git index set."""
import argparse
import hashlib
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('root')
parser.add_argument('--git-root')
args = parser.parse_args()
root = Path(args.root).resolve()
for folder in [root / 'evidence', root]:
    expected = set()
    for line in (folder / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = folder / name
        assert path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(folder)
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, name
        assert name not in expected, name
        expected.add(name)
    actual = {path.relative_to(folder).as_posix() for path in folder.rglob('*')
              if path.is_file() and path != folder / 'SHA256SUMS'}
    assert expected == actual, (expected - actual, actual - expected)
    print(f'HASH AND EXACT-SET PASS: {folder.name}: {len(expected)} manifest entries')
if args.git_root:
    repository = Path(args.git_root).resolve()
    prefix = root.relative_to(repository).as_posix() + '/'
    raw = subprocess.check_output(['git', 'ls-files', '-z', '--', prefix], cwd=repository).decode()
    tracked = {name[len(prefix):] for name in raw.split('\0') if name}
    actual = {path.relative_to(root).as_posix() for path in root.rglob('*') if path.is_file()}
    assert tracked == actual, (tracked - actual, actual - tracked)
    print(f'GIT INDEX EXACT-SET PASS: {len(actual)} files under {prefix}')
