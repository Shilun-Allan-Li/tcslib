import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import df3lib, df4lib
def load(h, path):
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
