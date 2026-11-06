"""closure.py <worktree> <rev> <old_rev> <targets.txt> <out_order.txt>
Import closure (TCSlib/audits modules) of the target modules at <rev>; print, in import order,
the modules to rebuild: those whose source differs between <old_rev> and <rev> (or is new), and
every closure module importing one of them transitively."""
import re, subprocess, sys
WT, REV, OLD, TG, OUT = sys.argv[1:6]
def show(rev, m):
    r = subprocess.run(['git', '-C', WT, 'show', f'{rev}:{m}.lean'], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
def imports(src):
    out = []
    for l in src.split('\n'):
        mm = re.match(r'^\s*(?:public\s+)?import\s+(\S+)', l)
        if mm:
            n = mm.group(1)
            if n.startswith(('TCSlib', 'audits')): out.append(n.replace('.', '/'))
    return out
deps, todo = {}, [l.strip() for l in open(TG) if l.strip()]
while todo:
    m = todo.pop()
    if m in deps: continue
    s = show(REV, m)
    if s is None: sys.exit(f'missing {m}')
    deps[m] = imports(s); todo += deps[m]
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in deps[m]: visit(d)
    order.append(m)
for m in sorted(deps): visit(m)
dirty = set()
for m in order:
    if show(REV, m) != show(OLD, m) or any(d in dirty for d in deps[m]): dirty.add(m)
res = [m for m in order if m in dirty]
open(OUT, 'w').write('\n'.join(res) + '\n')
print(len(deps), 'closure modules;', len(res), 'to rebuild')
