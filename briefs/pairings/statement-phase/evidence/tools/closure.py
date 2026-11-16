"""closure.py <repo> <rev> <module>...: TCSlib import closure (topological order) of the given modules at git rev."""
import sys, subprocess, re
repo, rev, *roots = sys.argv[1:]
def src(m):
    p = m.replace('.', '/') + '.lean'
    r = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{p}'], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
seen, order = set(), []
def visit(m):
    if m in seen: return
    seen.add(m)
    s = src(m)
    if s is None:
        print('MISSING', m, file=sys.stderr); return
    for imp in re.findall(r'^import\s+(\S+)', s, re.M):
        if imp.startswith('TCSlib.') or imp == 'TCSlib':
            visit(imp)
    order.append(m)
for r in roots: visit(r)
for m in order: print(m)
