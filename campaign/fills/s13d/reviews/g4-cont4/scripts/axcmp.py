import sys, re, json
from collections import Counter
def parse(p):
    t = open(p, encoding='utf-8').read()
    t = re.sub(r'\n\s+', ' ', t)
    res = {}
    for m in re.finditer(r"'(.+?)' depends on axioms: \[([^\]]*)\]", t):
        res[m.group(1)] = tuple(sorted(a.strip() for a in m.group(2).split(',')))
    for m in re.finditer(r"'(.+?)' does not depend on any axioms", t):
        res[m.group(1)] = ()
    return res, t
mine, t = parse(sys.argv[1]); worker, _ = parse(sys.argv[2])
norm = lambda n: re.sub(r'^_private\.[^.]+\.0\.', '', n)
M = {norm(k): v for k, v in mine.items()}; W = {norm(k): v for k, v in worker.items()}
nc = json.load(open(sys.argv[3]))
STD = {'propext', 'Classical.choice', 'Quot.sound'}
print('mine parsed', len(M), '; worker parsed', len(W))
print('sorryAx in mine:', [k for k, v in M.items() if 'sorryAx' in v])
print('outside the standard three (mine):', [k for k, v in M.items() if set(v) - STD])
print('tally (mine):', Counter(', '.join(v) if v else 'none' for v in M.values()))
print('names equal:', set(M) == set(W), sorted(set(M) ^ set(W))[:10])
print('axiom sets differ (mine vs worker):', [k for k in M if k in W and M[k] != W[k]])
newchg = ['Turing.' + n for n in nc['new'] + nc['changed']]
print('new/changed printed:', sum(1 for n in newchg if n in M), 'of', len(newchg))
for n in ['Turing.exists_zoneRebalanceTM', 'Turing.exists_zoneExtendTM']: print(n, M[n])
for m in re.finditer(r'SORRYSRC (\S+): (\[[^\]]*\])', t): print('SORRYSRC', m.group(1), m.group(2))
ext = re.findall(r'EXT (\S+): external (\d+) \(TCSlib (\d+)\); external privates (\[[^\]]*\]); external eqn/unfold lemmas (\[[^\]]*\])', t)
print('EXT lines', len(ext), '; with external privates:', [e[0] for e in ext if e[3] != '[]'], '; with external eqn/unfold lemmas:', [(e[0], e[4]) for e in ext if e[4] != '[]'][:20])
