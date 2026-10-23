# usage: overlap.py <graph.json> <ours-module> <label=module,module> ...
import json, sys
g = json.load(open(sys.argv[1]))
rev = {}
for m, ds in g.items():
    for d in ds: rev.setdefault(d, []).append(m)
def down(ms):
    out = set(ms); st = list(ms)
    while st:
        m = st.pop()
        for d in rev.get(m, []):
            if d not in out: out.add(d); st.append(d)
    out.discard('TCSlib'); return out
def up(m):
    out = set(); st = [m]
    while st:
        x = st.pop()
        for d in g.get(x, []):
            if d not in out: out.add(d); st.append(d)
    return out
ours = down([sys.argv[2]]); upo = up(sys.argv[2])
print('ours (changed + downstream):', sorted(ours))
for a in sys.argv[3:]:
    lab, ms = a.split('=', 1); ms = ms.split(',')
    th = down(ms)
    print(f'{lab}: changed {ms}; closure {len(th)}; shared with ours: {sorted(th & ours)}; '
          f'touches our upstream: {sorted(set(ms) & upo)}; ours upstream of theirs: {any(sys.argv[2] in up(m) for m in ms)}')
