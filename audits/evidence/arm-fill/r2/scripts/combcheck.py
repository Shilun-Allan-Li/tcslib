"""How round 1's combined screen output was formed: is it the full-population output verbatim
followed by exactly the supplement's pairs that involve a file of the supplement population not in
the full population? usage: python3 -I combcheck.py <full.out> <supp.out> <combined.out> <supp-pop> <full-pop>"""
import sys
full, supp, comb, sp, fp = sys.argv[1:6]
F = open(full, encoding='utf-8').read().split('\n'); C = open(comb, encoding='utf-8').read().split('\n')
ok1 = C[:len(F) - 1] == F[:-1] if F[-1] == '' else C[:len(F)] == F
extra = {l.strip() for l in open(sp) if l.strip()} - {l.strip() for l in open(fp) if l.strip()}
fl = lambda p: p.replace('TCSlib/Complexity/', '').replace('/', '__')
ex = {fl(p) for p in extra}
S = [l for l in open(supp, encoding='utf-8').read().split('\n') if '::' in l]
T = [l for l in C[len(F) - 1:] if '::' in l]
want = [l for l in S if any(x + '::' in l for x in ex)]
print(f'combined begins with the full output verbatim: {ok1}; extra supplement files: {sorted(ex)}; '
      f'supplement pairs touching them: {len(want)}; appended pairs: {len(T)}; identical: {want == T}')
