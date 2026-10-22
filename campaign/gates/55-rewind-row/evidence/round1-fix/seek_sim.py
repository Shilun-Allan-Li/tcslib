"""Gate 55 review: simulate skipBackTM's and rewindTM's tables on one tape (head trace only).
Tables transcribed from Build/Catalog (skipBackTM) and Build/Rewind (rewindTM) at 518769e9."""
from itertools import product
def run(table, q0, tape, pos, fuel=50):
    q, t, trace = q0, 0, [pos]
    while q != 'done' and t < fuel:
        sym = tape(pos); q, m = table(q, sym); pos += m; t += 1; trace.append(pos)
    return q, t, pos, trace
def skipBack(q, s):
    if q == 'run': return 'gap', -1
    if q == 'gap': return 'back', -1
    if q == 'back': return ('back', -1) if s is not None else ('done', +1)
def rewind(q, s):
    if q == 'start': return 'back', -1
    if q == 'back': return ('back', -1) if s is not None else ('done', +1)
buf = lambda u: (lambda z: u[z] if 0 <= z < len(u) else None)
out = []
bad_rw = bad_sb0 = 0
for L in range(0, 6):
    for u in product('ab', repeat=L):
        for p0 in range(0, L + 1):
            q, t, pos, tr = run(rewind, 'start', buf(u), p0)
            if not (q == 'done' and pos == 0 and t == p0 + 2): bad_rw += 1
            q2, t2, pos2, tr2 = run(skipBack, 'run', buf(u), p0)
            if p0 == 0 and pos2 != -1: bad_sb0 += 1
            if L <= 2 and len(set(u)) <= 1:
                out.append(f'u={"".join(u) or "[]"} p0={p0}: rewind {tr} (t={t}); skipBack {tr2} (t={t2}, end {pos2})')
out.append(f'rewind: start at any p0 <= |u| (|u| <= 5, all words over a,b) reaches done at 0 in p0+2 steps; failures: {bad_rw}')
out.append(f'skipBack from p0 = 0 stops at -1 in every case; failures: {bad_sb0}')
print('\n'.join(out))
