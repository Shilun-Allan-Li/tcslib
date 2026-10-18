"""Downstream replay closure (root TCSlib excluded) of each commit's changed modules, from the
commit's own tree, and its overlap with a given module set.
usage: python3 -I prclosures.py <repo> <base-of-diff> <ours-file> <label=commit>..."""
import re, subprocess, sys
repo, against, ours_f = sys.argv[1:4]
ours = set(l.strip() for l in open(ours_f) if l.strip())
def git(*a, inp=None):
    return subprocess.run(['git', '-C', repo, *a], capture_output=True, text=True, input=inp).stdout
def graph(c):
    files = [p for p in git('ls-tree', '-r', '--name-only', c, 'TCSlib').split('\n') if p.endswith('.lean')]
    files.append('TCSlib.lean') if git('cat-file', '-t', f'{c}:TCSlib.lean').strip() == 'blob' else None
    g = {}
    for p in files:
        src = git('show', f'{c}:{p}')
        imps = []
        for line in src.split('\n'):
            m = re.match(r'^import\s+(\S+)', line.strip())
            if m and m.group(1).startswith('TCSlib'): imps.append(m.group(1).replace('.', '/'))
        g[p[:-5]] = imps
    return g
for arg in sys.argv[4:]:
    lab, c = arg.split('=')
    mb = git('merge-base', against, c).strip()
    changed = [p[:-5] for p in git('diff', '--name-only', mb, c).split('\n') if p.endswith('.lean') and p.startswith('TCSlib')]
    g = graph(c); rev = {}
    for m, ds in g.items():
        for d in ds: rev.setdefault(d, set()).add(m)
    down, todo = set(), list(changed)
    while todo:
        m = todo.pop()
        if m in down: continue
        down.add(m); todo.extend(rev.get(m, ()))
    down.discard('TCSlib')
    print(f'{lab} {c[:8]} (merge-base with tip {mb[:8]}): changed {changed}; replay closure {len(down)}; overlap with ours: {sorted(down & ours) or "none"}')
