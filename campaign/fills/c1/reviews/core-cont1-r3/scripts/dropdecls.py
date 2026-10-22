"""Remove named declarations (each from its docstring to the line before the next docstring or the
target's docstring) from an overlay-shaped file, keeping everything else byte for byte.
usage: python3 -I dropdecls.py <in> <out> <name> [name ...]"""
import re, sys
src, out, drop = sys.argv[1], sys.argv[2], set(sys.argv[3:])
L = open(src, encoding='utf-8').read().split('\n')
starts = [i for i, l in enumerate(L) if l.startswith('/--')]
keep = [True] * len(L); found = set()
for n, s in enumerate(starts):
    e = starts[n + 1] if n + 1 < len(starts) else len(L)
    head = '\n'.join(L[s:e])
    m = re.search(r'^private (?:theorem|def|instance|lemma) (\S+)', head, re.M)
    if m and m.group(1) in drop:
        found.add(m.group(1))
        for i in range(s, e): keep[i] = False
assert found == drop, drop - found
res = [l for l, k in zip(L, keep) if k]
open(out, 'w', encoding='utf-8').write('\n'.join(res))
print('dropped', sorted(found), '; lines', len(L), '->', len(res))
