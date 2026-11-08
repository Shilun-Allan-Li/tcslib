import sys, re, os
# usage: topo.py <repo root> <root module>...  -> prints own modules in dependency order
root, roots = sys.argv[1], sys.argv[2:]
def p(m): return f'{root}/EndStatement.lean' if m == 'EndStatement' else f'{root}/{m.replace(".", "/")}.lean'
def deps(m):
    return [d for d in re.findall(r'(?m)^(?:public )?import (\S+)', open(p(m), encoding='utf-8').read())
            if d.startswith('ThreeSumApsp') or d == 'EndStatement']
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in deps(m): visit(d)
    order.append(m)
for r in roots: visit(r)
print(' '.join(order))
