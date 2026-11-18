"""Verify exact committed io-sprg paths and SHA256 bytes, including Unicode paths.

Mac root adaptation, 2026-11-18. No Lean; streams git cat-file without buffering
the entire payload. Writes only the requested evidence JSON, after verification.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('delivery')
ap.add_argument('--out', required=True)
a = ap.parse_args()
repo = Path(a.delivery)
prefix = 'inbox/fills/io-sprg/'
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
folder = repo / prefix
expected = {}
for line in (folder / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    assert name not in expected and not name.startswith('./')
    expected[name] = digest
expected['SHA256SUMS'] = hashlib.sha256((folder / 'SHA256SUMS').read_bytes()).hexdigest()
paths = subprocess.check_output(
    ['git', 'ls-tree', '-rz', '--name-only', head, '--', prefix], cwd=repo)
actual = {p.decode()[len(prefix):] for p in paths.split(b'\0') if p}
assert actual == set(expected), (actual - set(expected), set(expected) - actual)
p = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=repo,
                     stdin=subprocess.PIPE, stdout=subprocess.PIPE)
mismatches = []
for name, digest in sorted(expected.items()):
    p.stdin.write((head + ':' + prefix + name + '\n').encode())
    p.stdin.flush()
    header = p.stdout.readline().split()
    assert len(header) == 3 and header[1] == b'blob', header
    remaining = int(header[2])
    h = hashlib.sha256()
    while remaining:
        chunk = p.stdout.read(min(remaining, 1048576))
        assert chunk
        h.update(chunk)
        remaining -= len(chunk)
    assert p.stdout.read(1) == b'\n'
    if h.hexdigest() != digest:
        mismatches.append(name)
p.stdin.close()
assert p.wait() == 0 and not mismatches, mismatches
result = dict(exchange_commit=head, payload_files=len(expected),
              exact_committed_path_set=True, committed_sha256_mismatches=mismatches,
              path_encoding='NUL-delimited git paths, preserving Unicode filenames')
Path(a.out).write_text(json.dumps(result, indent=1) + '\n')
print(json.dumps(result))
