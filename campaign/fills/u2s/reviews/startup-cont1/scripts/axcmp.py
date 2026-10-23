"""Compare two #print axioms outputs by declaration. usage: python3 -I axcmp.py <mine> <worker>"""
import re, sys
PR = re.compile(r"'([^'\s]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
def norm(n): return re.sub(r'^_private\.[^.]+(?:\.[^.]+)*?\.0\.', '', n)
def prints(t):
    d = {}
    for m in PR.finditer(t):
        d[norm(m.group(1))] = ', '.join(x.strip() for x in (m.group(2) or '').split(',') if x.strip())
    return d
a = prints(open(sys.argv[1], encoding='utf-8').read()); b = prints(open(sys.argv[2], encoding='utf-8').read())
print('mine', len(a), 'worker', len(b))
common = sorted(set(a) & set(b))
print('common', len(common), '; differing prints:', [n for n in common if a[n] != b[n]] or 'none')
print('only mine:', sorted(set(a) - set(b))); print('only worker:', sorted(set(b) - set(a)))
for n in ('Turing.exists_selfStartupTMK', 'Turing.ss_serialized_layout'):
    print(n, 'mine:', a.get(n), '| worker:', b.get(n))
