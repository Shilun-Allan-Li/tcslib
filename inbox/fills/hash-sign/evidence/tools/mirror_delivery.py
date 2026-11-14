import hashlib
import json
import pathlib
import shutil
import sys

source = pathlib.Path(sys.argv[1]).resolve()
target = pathlib.Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange/inbox/fills/hash-sign')
assert source.name == 'hash-sign' and (source/'REPORT.md').is_file()
assert (source/'evidence/SHA256SUMS').is_file()
assert not target.is_symlink()
target.mkdir(parents=True, exist_ok=True)
assert all(not p.is_symlink() for p in source.rglob('*'))
assert all(not p.is_symlink() for p in target.rglob('*'))
expected = {p.relative_to(source).as_posix(): p for p in source.rglob('*') if p.is_file()}
old = {p.relative_to(target).as_posix(): p for p in target.rglob('*') if p.is_file()}
removed = sorted(set(old) - set(expected))
for name in removed:
    old[name].unlink()
for name, path in expected.items():
    out = target/name
    out.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(path, out)
actual = {p.relative_to(target).as_posix(): p for p in target.rglob('*') if p.is_file()}
assert set(actual) == set(expected)
for name, path in expected.items():
    assert hashlib.sha256(path.read_bytes()).digest() == hashlib.sha256(actual[name].read_bytes()).digest(), name
manifest = target/'evidence/SHA256SUMS'
rows = dict(line.split('  ',1)[::-1] for line in manifest.read_text().splitlines())
ev_actual = {p.relative_to(target/'evidence').as_posix() for p in (target/'evidence').rglob('*') if p.is_file() and p != manifest}
assert set(rows) == ev_actual
assert all(hashlib.sha256((target/'evidence'/name).read_bytes()).hexdigest() == digest for name,digest in rows.items())
print(json.dumps(dict(destination=str(target), files=len(expected), removed_stale_own_paths=removed,
    byte_identical_to_final_snapshot=True, evidence_manifest_exact=True, passed=True),indent=2))
