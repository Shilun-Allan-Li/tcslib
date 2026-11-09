"""fillinputs.py <repo> <rev> <module path, e.g. TCSlib/Complexity/SpaceComplexity/WindowClock> <outdir>
A fill's build inputs at a revision, read with `git show` (nothing checked out):
  order.txt        the upstream closure of the owned module and of every module downstream of it\n                   (the root `TCSlib` excluded), in topological order;
  roots.txt        the Mathlib modules imported by that closure, sorted;
  base-sorries.txt per module of the closure (in order), the declarations whose body contains
                   `sorry`, as `<path after TCSlib/Complexity/>: <count>: <names>`."""
import sys, os, re, subprocess
repo, rev, root, outd = sys.argv[1:5]
def show(path):
    return subprocess.run(['git', '-C', repo, 'show', f'{rev}:{path}.lean'], capture_output=True, text=True, check=True).stdout
cache = {}
def imports(mod):
    if mod not in cache:
        tc, ml = [], []
        for l in show(mod).split('\n'):
            m = re.match(r'^import\s+(\S+)', l)
            if m:
                n = m.group(1)
                (tc if n.startswith('TCSlib') else ml).append(n)
        cache[mod] = ([n.replace('.', '/') for n in tc], ml)
    return cache[mod]
# every module downstream of the owned one (the root `TCSlib` excluded), then the upstream closure
# of the owned module and of all of those, in topological order
allmods = [f[:-5] for f in subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', rev, 'TCSlib'],
           capture_output=True, text=True, check=True).stdout.split() if f.endswith('.lean')]
rev_ = {}
for m in allmods:
    for d in imports(m)[0]: rev_.setdefault(d, set()).add(m)
down, todo = set(), [root]
while todo:
    m = todo.pop()
    if m in down: continue
    down.add(m); todo.extend(rev_.get(m, ()))
down.discard('TCSlib')
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in imports(m)[0]: visit(d)
    order.append(m)
for m in sorted(down): visit(m)
roots = sorted({r for m in order for r in imports(m)[1] if r.startswith('Mathlib')})
def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: out.append(src[i])
        i += 1
    return ''.join(out)
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|example)\s+([^\s(:{\[]*)', re.M)
lines = []
for m in order:
    code = strip(show(m)).split('\n')
    cur, names = None, []
    for l in code:
        d = DECL.match(l)
        if d: cur = (d.group(1) or '(anonymous)') + (' [private]' if re.match(r'^(?:@\[[^\]]*\]\s*)*private\b', l) else '')
        elif re.match(r'^(end|namespace|section)\b', l): cur = None
        if cur and re.search(r'\bsorry\b', l.split('--')[0]) and (not names or names[-1] != cur): names.append(cur)
    if names: lines.append(f"{m.replace('TCSlib/Complexity/', '')}: {len(names)}: {', '.join(names)}")
os.makedirs(outd, exist_ok=True)
open(os.path.join(outd, 'order.txt'), 'w').write(''.join(m + '\n' for m in order))
open(os.path.join(outd, 'roots.txt'), 'w').write(''.join(r + '\n' for r in roots))
total = sum(int(l.split(': ')[1]) for l in lines)
open(os.path.join(outd, 'base-sorries.txt'), 'w').write(''.join(l + '\n' for l in lines) + f'TOTAL {total}\n')
print(f'order {len(order)}, roots {len(roots)}, sorried declarations {sum(int(l.split(": ")[1]) for l in lines)} in {len(lines)} modules')
