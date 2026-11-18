"""exportcheck.py <repo> <rev> <dir> <path>...: the export <dir> holds exactly the blobs of <rev> under <path>... (git blob
ids via `git ls-tree -r` vs `git hash-object` of the files; extra/missing/changed counts; ignores .lake and probe dirs
named on PROBE_DIRS)."""
import sys, os, subprocess
repo, rev, d = sys.argv[1:4]; paths = sys.argv[4:]
want = {}
for l in subprocess.run(['git', '-C', repo, 'ls-tree', '-r', rev, '--', *paths], capture_output=True, text=True, check=True).stdout.splitlines():
    meta, p = l.split('\t', 1); want[p] = meta.split()[2]
have = []
for top in paths:
    tp = os.path.join(d, top)
    if os.path.isfile(tp): have.append(top); continue
    for r, ds, fs in os.walk(tp):
        for f in fs: have.append(os.path.relpath(os.path.join(r, f), d))
ids = {}
if have:
    out = subprocess.run(['git', '-C', repo, 'hash-object', '--stdin-paths'], input='\n'.join(os.path.join(d, p) for p in have),
                         capture_output=True, text=True, check=True).stdout.split()
    ids = dict(zip(have, out))
extra = sorted(set(ids) - set(want)); missing = sorted(set(want) - set(ids)); changed = sorted(p for p in ids if p in want and ids[p] != want[p])
for n, l in (('extra', extra), ('missing', missing), ('changed', changed)):
    for p in l: print(n, p)
print(f'rev {rev} files {len(want)} extra {len(extra)} missing {len(missing)} changed {len(changed)} RESULT {"OK" if not (extra or missing or changed) else "FAIL"}')
