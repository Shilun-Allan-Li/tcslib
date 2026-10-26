import sys, os, subprocess, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import df3lib, df4lib
ref, path = sys.argv[1], sys.argv[2]
revs = subprocess.run(['git', 'log', '--first-parent', '--format=%H %cs', ref, '--', path], capture_output=True, text=True, check=True).stdout.split('\n')
revs = [r.split() for r in revs if r][::-1]
def load(h):
    r = subprocess.run(['git', 'show', f'{h}:{path}'], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
def model(t):
    c3 = df3lib.chunks(t); c4 = df4lib.chunks(t)
    assert len(c3) == len(c4)
    last = {}
    for i, (s, _, _) in enumerate(c3): last[s] = i
    vis = {c4[i][0] for i in last.values()}
    coll = {c4[i][0] for i, (s, _, _) in enumerate(c3) if sum(1 for x in c3 if x[0] == s) > 1}
    return {n: (p, t) for n, p, t in c4}, vis, coll
prev = None
for h, d in revs:
    t = load(h)
    if t is None: prev = None; continue
    cur = model(t)
    if prev is not None:
        (A, visA, collA), (B, visB, collB) = prev[1], cur
        coll = collA | collB
        missed = []
        for n in sorted(set(A) | set(B)):
            if n not in coll: continue
            a, b = A.get(n), B.get(n)
            if a == b: continue
            kind = 'added' if a is None else 'removed' if b is None else ('statement' if df4lib.stmt(a[1]) != df4lib.stmt(b[1]) else 'body')
            seen = (a is None or n in visA) and (b is None or n in visB)
            missed.append((n, kind, 'visible-to-v3' if seen else 'INVISIBLE-to-v3'))
        if missed: print(prev[0][:8], '->', h[:8], d, missed)
    prev = ((h, d), cur)
print('done', path, len(revs), 'revisions')
