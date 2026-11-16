"""Write and verify the delivery manifests (python3 -I).

Usage: manifests.py <delivery-dir>   (e.g. inbox/fills/gsw-security)
Writes <dir>/evidence/SHA256SUMS over every file under evidence/ except itself, then
<dir>/SHA256SUMS over every delivered file under <dir> except itself (evidence/SHA256SUMS
included), paths relative to the manifest's directory, sorted, no leading `./`, in the
`shasum -a 256` format. Then re-reads both and checks that the set of listed paths equals the
set of files on disk exactly (nothing missing, nothing extra) and that every hash matches.
"""
import hashlib
from pathlib import Path
import sys

root = Path(sys.argv[1])


def files_under(d, skip):
    return sorted(p for p in d.rglob('*') if p.is_file() and p != skip)


def write(d):
    man = d / 'SHA256SUMS'
    rows = [f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(d).as_posix()}'
            for p in files_under(d, man)]
    man.write_text('\n'.join(rows) + '\n')
    return man


def verify(d):
    man = d / 'SHA256SUMS'
    listed = {}
    for line in man.read_text().splitlines():
        h, path = line.split('  ', 1)
        assert not path.startswith('./'), path
        listed[path] = h
    disk = {p.relative_to(d).as_posix() for p in files_under(d, man)}
    missing, extra = sorted(disk - set(listed)), sorted(set(listed) - disk)
    bad = [p for p in listed if p in disk and
           hashlib.sha256((d / p).read_bytes()).hexdigest() != listed[p]]
    ok = not missing and not extra and not bad
    print(f'{man}: {len(listed)} entries; unlisted on disk {len(missing)}, listed but absent '
          f'{len(extra)}, hash mismatches {len(bad)} -> {"OK" if ok else "FAIL"}')
    for p in missing + extra + bad:
        print('  ', p)
    return ok


write(root / 'evidence')
write(root)
ok = verify(root / 'evidence') & verify(root)
sys.exit(0 if ok else 1)
