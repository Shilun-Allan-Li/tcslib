"""stale_closure.py <worktree> <order-file> <summary.tsv>... (gsw-6b-statements, new): modules of the
order whose current source (in <worktree>) differs from the source SHA-256 recorded at their last
successful build in the given pbuild summaries (last row wins), plus every module downstream of one
(TCSlib imports), printed in the order's order. The addendum's "rebuild every module whose source
differs from the source its olean was built from, then everything downstream of it"."""
import sys, re, os, hashlib
wt, order, sums = sys.argv[1], sys.argv[2], sys.argv[3:]
mods = [l.strip() for l in open(order) if l.strip()]
built = {}
for s in sums:
    for l in open(s):
        f = l.rstrip('\n').split('\t')
        if len(f) >= 12 and f[1] == 'rc=0' and f[2] == 'errors=0': built[f[0]] = f[11]
def src(m):
    p = os.path.join(wt, m + '.lean')
    return hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
def imps(m):
    p = os.path.join(wt, m + '.lean')
    return [x.replace('.', '/') for x in re.findall(r'^import\s+(TCSlib\S*)', open(p, encoding='utf8').read(), re.M)] if os.path.exists(p) else []
stale = {m for m in mods if built.get(m) != src(m)}
changed = True
while changed:
    changed = False
    for m in mods:
        if m not in stale and any(d in stale for d in imps(m)): stale.add(m); changed = True
for m in mods:
    if m in stale: print(m)
print(f'# {len(stale)} stale of {len(mods)}', file=sys.stderr)
