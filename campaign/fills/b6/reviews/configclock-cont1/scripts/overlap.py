"""Open PRs' replay closures (downstream of their changed modules, at the tip) vs this landing's.
usage: python3 -I overlap.py <repo> <tip worktree> <graph dir> <out dir>"""
import os, subprocess, sys
repo, wt, gdir, outd = sys.argv[1:5]
sys.path.insert(0, gdir)
from graph import imports_of  # noqa: E402
mods = {}
for d, _, fs in os.walk(os.path.join(wt, 'TCSlib')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f)
            mods[os.path.relpath(p, wt)[:-5].replace(os.sep, '.')] = [i for i in imports_of(p) if i.startswith('TCSlib')]
rev = {}
for m, imps in mods.items():
    for i in imps: rev.setdefault(i, set()).add(m)
def down(ts):
    s, todo = set(), list(ts)
    while todo:
        m = todo.pop()
        if m in s: continue
        s.add(m); todo.extend(rev.get(m, ()))
    s.discard('TCSlib'); return s
mine = down(['TCSlib.Complexity.SpaceComplexity.WindowClock'])
print('this landing:', sorted(mine))
tip = 'b175e512ee285c491daddcd20399507a47c644dd'
for pr, b in [('#124', 'origin/lean/seam-layout'), ('#129', 'lean/c1-un-partial'), ('#130', 'lean/u2s-partial'),
              ('#131', 'lean/canon-cont6-partial'), ('#132', 'lean/un-u2s-api')]:
    g = lambda *a: subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True).stdout.strip()
    mb = g('merge-base', b, tip)
    files = [f[:-5].replace('/', '.') for f in g('diff', '--name-only', mb, b, '--', 'TCSlib').split('\n') if f.endswith('.lean')]
    old = [f for f in files if f in mods]; new = [f for f in files if f not in mods]
    cl = down(old)
    print(f"{pr} {b} {g('rev-parse', '--short', b)} (merge base {mb[:8]}): changed {files}; new at tip {new}; "
          f"closure at tip {len(cl)} modules (+{len(new)} new); overlap with this landing: {sorted(cl & mine)}")
