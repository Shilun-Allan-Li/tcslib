"""treecheck.py <tree> <order> <records.jsonl> <repo> <rev> <snapshot-out> [<snapshot-ref>]
Base-tree check in the form of the r1 reviewer's logs/restore-base-check.txt: for every module of
<order>, its last record in <records.jsonl> must be rc 0 at the <rev> source hash, and the tree's
.olean must have that record's object hash. Also lists .olean files outside <order> (PFR/ excluded:
the vendored dependency tree is not rebuilt), empty directories, and writes a full snapshot
(SHA-256 of every file under <tree>); with <snapshot-ref>, the snapshot must equal it."""
import sys, os, json, hashlib, subprocess
tree, order, recs, repo, rev, snap = sys.argv[1:7]
ref = sys.argv[7] if len(sys.argv) > 7 else None
mods = [l.strip() for l in open(order) if l.strip()]
last = {}
for l in open(recs):
    r = json.loads(l)
    if 'module' in r: last[r['module']] = r
sha = lambda b: hashlib.sha256(b).hexdigest()
def src(m):
    p = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{m}.lean'], capture_output=True)
    return sha(p.stdout) if p.returncode == 0 else None
badrec, badobj, missing = [], [], []
for m in mods:
    r = last.get(m)
    if r is None or r['rc'] != 0 or r['source_sha256'] != src(m): badrec.append(m)
    p = os.path.join(tree, m + '.olean')
    if not os.path.exists(p): missing.append(m); continue
    if r is None or sha(open(p, 'rb').read()) != r['object_sha256']: badobj.append(m)
files = {}
for d, ds, fs in os.walk(tree):
    for f in fs:
        p = os.path.join(d, f); files[os.path.relpath(p, tree)] = sha(open(p, 'rb').read())
empty = sorted(os.path.relpath(d, tree) for d, ds, fs in os.walk(tree) if not ds and not fs)
mset = {m + '.olean' for m in mods}
extra = sorted(f for f in files if f not in mset and not f.startswith('PFR/'))
with open(snap, 'w') as o:
    for f in sorted(files): o.write(f'{files[f]}  {f}\n')
print(f'{rev[:8]} order {len(mods)}; files under tree {len(files)}; record not rc 0 at source: '
      f'{len(badrec)} {badrec[:5]}; olean differs from record: {len(badobj)} {badobj[:5]}; '
      f'missing: {len(missing)} {missing[:5]}; oleans outside order (non-PFR): {len(extra)} {extra[:5]}; '
      f'empty dirs: {len(empty)} {empty[:5]}')
ok = not (badrec or badobj or missing or extra or empty)
if ref:
    same = open(ref).read() == open(snap).read()
    print(f'snapshot equals reference {os.path.basename(ref)}: {same}'); ok = ok and same
print('RESULT', 'OK' if ok else 'FAIL')
