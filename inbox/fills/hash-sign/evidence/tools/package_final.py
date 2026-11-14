import hashlib
import json
import pathlib
import shutil
import subprocess
import sys
import zipfile

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
master = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign')
dest = pathlib.Path(sys.argv[1])
archive = pathlib.Path(sys.argv[2])
commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
verification = json.loads((master / 'evidence/logs/final-verification.json').read_text())
assert verification['passed'] and verification['source_commit'] == commit
report = (master / 'REPORT.md').read_text()
assert report.startswith('# hash-sign — final') and 'PENDING' not in report
if dest.exists() or archive.exists():
    raise SystemExit('Refusing to replace existing final snapshot/archive')
dest.mkdir(parents=True)
shutil.copy2(master / 'REPORT.md', dest / 'REPORT.md')
shutil.copytree(master / 'patches', dest / 'patches')
shutil.copytree(master / 'evidence', dest / 'evidence')
base = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
paths = subprocess.check_output(['git', 'diff', '--name-only', base, commit], cwd=repo, text=True).splitlines()
for path in paths:
    target = dest / 'src' / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo))
ev = dest / 'evidence'
manifest = ev / 'SHA256SUMS'
files = sorted(p for p in ev.rglob('*') if p.is_file() and p != manifest)
manifest.write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(ev).as_posix() + '\n' for p in files))
entries = dict(line.split('  ', 1)[::-1] for line in manifest.read_text().splitlines())
actual = {p.relative_to(ev).as_posix() for p in ev.rglob('*') if p.is_file() and p != manifest}
assert set(entries) == actual
assert all(hashlib.sha256((ev / p).read_bytes()).hexdigest() == digest for p, digest in entries.items())
for path in paths:
    assert (dest / 'src' / path).read_bytes() == subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)
payload_manifest = dest / 'PAYLOAD-SHA256SUMS'
payload_files = sorted(p for p in dest.rglob('*') if p.is_file() and p != payload_manifest)
payload_manifest.write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(dest).as_posix() + '\n' for p in payload_files))
payload_rows = dict(line.split('  ', 1)[::-1] for line in payload_manifest.read_text().splitlines())
assert set(payload_rows) == {p.relative_to(dest).as_posix() for p in payload_files}
assert all(hashlib.sha256((dest / name).read_bytes()).hexdigest() == digest for name,digest in payload_rows.items())
archive.parent.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for path in sorted(p for p in dest.rglob('*') if p.is_file()):
        z.write(path, 'hash-sign/' + path.relative_to(dest).as_posix())
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    expected = {'hash-sign/' + p.relative_to(dest).as_posix() for p in dest.rglob('*') if p.is_file()}
    assert set(z.namelist()) == expected
    assert all(name.startswith('hash-sign/') for name in z.namelist())
result = dict(source_commit=commit, source_files=len(paths), evidence_files=len(files),
    payload_files=len(expected), archive=str(archive), archive_bytes=archive.stat().st_size,
    archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(), passed=True)
print(json.dumps(result, indent=2))
