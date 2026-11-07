"""checksdiff.py <base.out> <head.out>: join multi-line `#print axioms` records and compare per declaration."""
import sys, re
def parse(p):
    txt = open(p).read()
    recs, cur = {}, None
    for line in txt.splitlines():
        m = re.match(r"^'([^']+)' (depends on axioms: |does not depend on any axioms)(.*)$", line)
        if m:
            cur = m.group(1); recs[cur] = (m.group(2) + m.group(3)).strip(); continue
        if cur and recs[cur].startswith('depends') and not recs[cur].endswith(']'):
            recs[cur] += ' ' + line.strip(); continue
        cur = None
    norm = {}
    for k, v in recs.items():
        ax = re.findall(r'[\w.]+', v.split(':', 1)[1]) if ':' in v else []
        norm[k] = sorted(ax)
    return norm, txt
b, bt = parse(sys.argv[1]); h, ht = parse(sys.argv[2])
STD = sorted(['propext', 'Classical.choice', 'Quot.sound'])
def cls(ax): return 'SORRY' if 'sorryAx' in ax else ('STD' if set(ax) <= set(STD) else 'OTHER:' + ','.join(ax))
print(f'base records {len(b)}, head records {len(h)}')
for k in sorted(set(b) - set(h)): print('REMOVED', k, cls(b[k]))
for k in sorted(set(h) - set(b)): print('ADDED', k, cls(h[k]))
better, worse, other = [], [], []
for k in sorted(set(b) & set(h)):
    if b[k] == h[k]: continue
    cb, ch = cls(b[k]), cls(h[k])
    (better if (cb == 'SORRY' and ch == 'STD') else worse if (cb == 'STD' and ch != 'STD') or (ch == 'SORRY' and cb != 'SORRY') else other).append((k, cb, ch))
print(f'BECAME STANDARD ({len(better)}):'); [print('  ', k) for k, _, _ in better]
print(f'GOT WORSE ({len(worse)}):'); [print('  ', k, a, '->', c) for k, a, c in worse]
print(f'OTHER CHANGES ({len(other)}):'); [print('  ', k, a, '->', c) for k, a, c in other]
print('base sorryAx records:', sum('sorryAx' in v for v in b.values()), ' head sorryAx records:', sum('sorryAx' in v for v in h.values()))
nb = [l for l in bt.splitlines() if not l.startswith("'") and not l.startswith(' ') and l.strip()]
nh = [l for l in ht.splitlines() if not l.startswith("'") and not l.startswith(' ') and l.strip()]
print('non-axiom lines base/head:', len(nb), len(nh))
for l in sorted(set(nh) - set(nb)): print('  NEW non-axiom line:', l[:200])
for l in sorted(set(nb) - set(nh)): print('  GONE non-axiom line:', l[:200])
