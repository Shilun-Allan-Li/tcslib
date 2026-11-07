"""downstream.py <worktree> <files.txt> <out>: every module of the repository (TCSlib/, audits/) that
imports one of the given files, transitively, at the worktree's HEAD; in import order."""
import re, subprocess, sys
WT, FILES, OUT = sys.argv[1:4]
ls = subprocess.run(['git', '-C', WT, 'ls-files', 'TCSlib', 'audits', 'TCSlib.lean'], capture_output=True, text=True).stdout.split()
mods = {p[:-5] for p in ls if p.endswith('.lean')}
deps = {}
for m in mods:
    src = open(f"{WT}/{m}.lean", encoding='utf-8').read()
    deps[m] = [x.replace('.', '/') for x in re.findall(r'(?m)^\s*(?:public\s+)?import\s+(\S+)', src)
               if x.startswith(('TCSlib', 'audits')) and x.replace('.', '/') in mods]
seed = {l.strip()[:-5] for l in open(FILES) if l.strip()}
down = set(seed)
changed = True
while changed:
    changed = False
    for m, ds in deps.items():
        if m not in down and any(d in down for d in ds): down.add(m); changed = True
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in deps[m]: visit(d)
    if m in down: order.append(m)
for m in sorted(down): visit(m)
open(OUT, 'w').write('\n'.join(order) + '\n'); print(len(order), 'modules downstream of (and including) the files')
