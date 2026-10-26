import re, sys
t = open(sys.argv[1], encoding='utf-8').read()
pat = re.compile(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.S)
rows = [(m.group(1), ' '.join(m.group(3).split()) if m.group(3) is not None else '(none)') for m in pat.finditer(t)]
print(len(rows), 'prints')
std = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [r for r in rows if r[1] != '(none)' and not set(x.strip() for x in r[1].split(',')) <= std]
print('outside the standard three:', bad)
for n, a in rows: print(f'{n:45s} {a}')
