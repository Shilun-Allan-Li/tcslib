"""assemble.py <stage-dir> <evidence-src-root> <evidence-item>...: copies the listed evidence items
(paths relative to <evidence-src-root>) into <stage-dir>/evidence/, writes evidence/SHA256SUMS (every
evidence file except itself, paths relative to evidence/), then the top-level SHA256SUMS (every file
under <stage-dir> except itself, relative paths, no leading ./), and checks that the delivered paths
equal the manifests' paths exactly."""
import sys, os, shutil, hashlib
stage, src = sys.argv[1], sys.argv[2]
ev = os.path.join(stage, 'evidence')
for it in sys.argv[3:]:
    s = os.path.join(src, it); d = os.path.join(ev, it)
    os.makedirs(os.path.dirname(d), exist_ok=True)
    if os.path.isdir(s):
        shutil.copytree(s, d, dirs_exist_ok=True, ignore=shutil.ignore_patterns('__pycache__', '*.olean', 'current.pid'))
    else:
        shutil.copy2(s, d)
def files(root, skip):
    out = []
    for dp, dn, fn in os.walk(root):
        for f in fn:
            p = os.path.relpath(os.path.join(dp, f), root)
            if p != skip: out.append(p)
    return sorted(out)
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
ef = files(ev, 'SHA256SUMS')
with open(os.path.join(ev, 'SHA256SUMS'), 'w') as f:
    for p in ef: f.write(f'{sha(os.path.join(ev, p))}  {p}\n')
tf = files(stage, 'SHA256SUMS')
with open(os.path.join(stage, 'SHA256SUMS'), 'w') as f:
    for p in tf: f.write(f'{sha(os.path.join(stage, p))}  {p}\n')
# path equality checks
m1 = [l.split('  ', 1)[1].rstrip('\n') for l in open(os.path.join(ev, 'SHA256SUMS'))]
assert m1 == files(ev, 'SHA256SUMS'), 'evidence manifest mismatch'
m2 = [l.split('  ', 1)[1].rstrip('\n') for l in open(os.path.join(stage, 'SHA256SUMS'))]
assert m2 == files(stage, 'SHA256SUMS'), 'top manifest mismatch'
assert not any(p.startswith('./') for p in m1 + m2)
print(f'evidence files {len(m1)}, delivered files {len(m2)} (+ top SHA256SUMS); manifests equal the delivered paths')
