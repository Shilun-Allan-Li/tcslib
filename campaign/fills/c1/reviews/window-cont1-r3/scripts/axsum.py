"""Summarize an axiom/ext probe output. usage: python3 -I axsum.py <out> [worker axioms log]"""
import re, sys, collections
PR = re.compile(r"^'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M | re.S)
def norm(n): return re.sub(r'^_private\.[^.]+(?:\.[^.]+)*?\.0\.', '', n)
def prints(t):
    d = {}
    for m in PR.finditer(t):
        d[norm(m.group(1))] = ', '.join(x.strip() for x in (m.group(2) or '').split(',') if x.strip())
    return d
t = open(sys.argv[1], encoding='utf-8').read()
ax = prints(t)
print('distinct axiom prints:', len(ax))
std = {'propext', 'Classical.choice', 'Quot.sound'}
bad = {n: a for n, a in ax.items() if a and not set(a.split(', ')) <= std}
print('outside [propext, Classical.choice, Quot.sound]:', bad or 'none')
print('sorryAx in any axiom list:', any('sorryAx' in a for a in ax.values()))
print('histogram:', dict(collections.Counter(a or '(none)' for a in ax.values())))
for n in ('Turing.exists_inputWindowCopyTM', 'Turing.iw_local'):
    print(n, '->', ax.get(n))
for l in t.split('\n'):
    if 'direct sorryAx users' in l: print(l.strip()[:200])
ext = re.findall(r'EXT (\S+): external (\d+) \(TCSlib (\d+)\); external privates \[([^\]]*)\]; external eqn/unfold lemmas \[([^\]]*)\]', t)
eq = sorted({x.strip() for e in ext for x in e[4].split(',') if x.strip()})
print('EXT lines:', len(ext), '; external privates reached:', sorted({x.strip() for e in ext for x in e[3].split(',') if x.strip()}) or 'none')
print('names flagged by the eqn/unfold heuristic (X.eq_*, X.match_*, ...):', eq)
m = re.search(r'EXTLIST total (\d+); TCSlib (\d+): \[(.*?)\]', t, re.S)
if m:
    names = [x.strip() for x in m.group(3).replace('\n', ' ').split(',') if x.strip()]
    print('EXTLIST total', m.group(1), '; TCSlib', m.group(2))
    open(sys.argv[1] + '.tcslib-consts.txt', 'w').write('\n'.join(names) + '\n')
if len(sys.argv) > 2:
    wax = prints(open(sys.argv[2], encoding='utf-8').read())
    print("worker's distinct prints:", len(wax), '; equal to mine (private prefix and whitespace normalized):', wax == ax)
    for n in sorted(set(ax) | set(wax)):
        if ax.get(n) != wax.get(n): print('   DIFF', n, ax.get(n), '|', wax.get(n))
