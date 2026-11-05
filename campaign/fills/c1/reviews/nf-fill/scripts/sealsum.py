"""Summarize the review's maximal seal runs (python3 -I).
usage: python3 -I sealsum.py <sealed .out> <unsealed .out> <alldefs> <reached defs file>"""
import re, sys
S = open(sys.argv[1], encoding='utf-8').read(); U = open(sys.argv[2], encoding='utf-8').read()
alld = [l.strip() for l in open(sys.argv[3], encoding='utf-8') if l.strip()]
reached = [l.strip() for l in open(sys.argv[4], encoding='utf-8') if l.strip()]
def res(T):
    d = {}
    for m in re.finditer(r'CONTROL_(PASS|FAIL) (\w+) (\S+)', T): d[(m.group(2), m.group(3))] = m.group(1)
    return d
s, u = res(S), res(U)
print('sealed: errors', len(re.findall(r': error', S)), '; warnings', re.findall(r':(\d+):\d+: warning: (.*)', S))
print('unsealed: errors', len(re.findall(r': error', U)), '; warnings', re.findall(r':(\d+):\d+: warning: (.*)', U))
for k in ['rfl', 'eqn', 'simp']:
    ks = [n for (kk, n) in s if kk == k]
    print(f'{k}: {len(ks)} controls; sealed FAIL {sum(s[(k, n)] == "FAIL" for n in ks)}; sealed PASS {sum(s[(k, n)] == "PASS" for n in ks)}; unsealed PASS {sum(u.get((k, n)) == "PASS" for n in ks)}')
good = {}
for (k, n), v in s.items():
    if v == 'FAIL' and u.get((k, n)) == 'PASS': good.setdefault(n, []).append(k)
print('sealed definitions with a control that fails sealed and closes unsealed:', sum(d in good for d in alld), 'of', len(alld))
print('  without one:', [d for d in alld if d not in good])
print('rfl controls failing unsealed (covered by eqn controls):', sorted(n for (k, n) in u if k == 'rfl' and u[(k, n)] == 'FAIL'))
print('  their eqn controls (unsealed / sealed):', [(n, u.get(('eqn', n)), s.get(('eqn', n))) for (k, n) in u if k == 'rfl' and u[(k, n)] == 'FAIL'])
print('eqn controls passing unsealed (recursive definitions):', sorted(n for (k, n) in u if k == 'eqn' and u[(k, n)] == 'PASS'))
print('simp erasure controls:', [(n, u.get(('simp', n)), s.get(('simp', n))) for (k, n) in s if k == 'simp'])
print('reached definitions (the walk, other-file TCSlib):', len(reached), '; each sealed with a working control:', all(r in good for r in reached))
print('  missing:', [r for r in reached if r not in good])
