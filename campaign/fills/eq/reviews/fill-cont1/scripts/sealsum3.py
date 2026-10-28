"""Summarize the review's maximal seal (mkseal3) runs (python3 -I).
usage: python3 -I sealsum3.py <sealed .out> <unsealed .out> <reached-defs file>"""
import re, sys
S = open(sys.argv[1], encoding='utf-8').read(); U = open(sys.argv[2], encoding='utf-8').read()
reached = [l.strip() for l in open(sys.argv[3], encoding='utf-8') if l.strip()]
def res(T):
    d = {}
    for m in re.finditer(r'CONTROL_(PASS|FAIL) (\w+) (\S+)', T): d[(m.group(2), m.group(3))] = m.group(1)
    return d
s, u = res(S), res(U)
print('sealed: errors', len(re.findall(r': error', S)), '; warnings', re.findall(r':(\d+):\d+: warning: (.*)', S))
print('unsealed: errors', len(re.findall(r': error', U)), '; warnings', re.findall(r':(\d+):\d+: warning: (.*)', U))
for k in ['rfl', 'eqn', 'simp']:
    ks = [n for (kk, n) in s if kk == k]
    print(f'{k}: {len(ks)} controls; sealed FAIL {sum(s[(k, n)] == "FAIL" for n in ks)}; unsealed PASS {sum(u.get((k, n)) == "PASS" for n in ks)}')
good = {n for (k, n) in s if s[(k, n)] == 'FAIL' and u.get((k, n)) == 'PASS'}
alln = {n for (k, n) in s}
print('definitions with a control that fails sealed and closes unsealed:', len(good), 'of', len(alln))
print('without one:', sorted(alln - good))
print('rfl controls failing unsealed (recursive; covered by eqn controls):', sorted(n for (k, n) in u if k == 'rfl' and u[(k, n)] == 'FAIL'))
print('reached definitions (the walk):', len(reached), '; each sealed with a working control:', all(r in good for r in reached))
print('  missing:', [r for r in reached if r not in good])
