"""Map each diagnostic of an exact?/apply? probe run to its probe. Usage: probemap.py <probe.lean> <out>"""
import re, sys
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
marks = [(i + 1, l[3:]) for i, l in enumerate(L) if l.startswith('-- PROBE') or l.startswith('-- CONTROL')]
out = open(sys.argv[2], encoding='utf-8').read()
# split diagnostics: lines starting with the file prefix
diags = re.split(r'(?m)^(?=Probe/\S+\.lean:\d+:\d+: )', out)
by = {}
for d in diags:
    m = re.match(r'Probe/\S+\.lean:(\d+):\d+: (\w+): ', d)
    if not m: continue
    ln = int(m.group(1))
    owner = None
    for j, (a, name) in enumerate(marks):
        b = marks[j + 1][0] if j + 1 < len(marks) else 10**9
        if a < ln < b: owner = name
    if owner: by.setdefault(owner, []).append((m.group(2), ' '.join(d.split())[:260]))
for a, name in marks:
    res = by.get(name, [])
    kinds = [k for k, _ in res]
    if 'error' in kinds:
        first = next(t for k, t in res if k == 'error')
        print(f'{name}\n    -> NOT CLOSED: {first[:200]}')
    elif res:
        print(f'{name}\n    -> CLOSED: {res[0][1][:240]}')
    else:
        print(f'{name}\n    -> (no diagnostic)')
