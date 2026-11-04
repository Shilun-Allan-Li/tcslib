"""Re-derive the order list, the Mathlib roots and a text-level sorry census from `git show`.

Usage: python3 -I order.py <repo> <commit> <owned module path without .lean> <outdir>

The order list is the import closure of every module that imports the owned module (directly or
not), the owned module included, in a topological order (imports first; ties broken by the
reference list order when given, else by name). Everything is read with `git show <commit>:<path>`.
"""
import os
import re
import subprocess
import sys

repo, commit, owned, outdir = sys.argv[1:5]
ref = sys.argv[5] if len(sys.argv) > 5 else None


def git(*args):
    return subprocess.run(['git', '-C', repo] + list(args), check=True,
                          capture_output=True, text=True).stdout


files = [p for p in git('ls-tree', '-r', '--name-only', commit, 'TCSlib').split('\n')
         if p.endswith('.lean')]
files.append('TCSlib.lean') if 'TCSlib.lean' in git('ls-tree', '--name-only', commit) else None
src = {}
imps = {}
mlroots = {}
for p in files:
    m = p[:-5]
    text = git('show', f'{commit}:{p}')
    src[m] = text
    ti, mi = [], []
    for line in text.split('\n'):
        mm = re.match(r'^import\s+(\S+)', line.strip())
        if mm:
            n = mm.group(1)
            if n.startswith('TCSlib'):
                ti.append(n.replace('.', '/'))
            elif n.startswith('Mathlib'):
                mi.append(n)
    imps[m] = ti
    mlroots[m] = mi

# dependents of the owned module
dep = {owned}
changed = True
while changed:
    changed = False
    for m, ii in imps.items():
        if m not in dep and m != 'TCSlib' and any(i in dep for i in ii):
            dep.add(m)
            changed = True
# import closure
clo = set()
stack = list(dep)
while stack:
    m = stack.pop()
    if m in clo:
        continue
    clo.add(m)
    stack.extend(i for i in imps.get(m, []) if i not in clo)
missing = [m for m in clo if m not in imps]
# topological order
refidx = {}
if ref:
    for i, l in enumerate(open(ref).read().split()):
        refidx[l] = i
order = []
done = set()


def visit(m, path=()):
    if m in done:
        return
    for i in sorted(imps.get(m, []), key=lambda n: (refidx.get(n, 10**6), n)):
        visit(i, path + (m,))
    done.add(m)
    order.append(m)


for m in sorted(clo, key=lambda n: (refidx.get(n, 10**6), n)):
    visit(m)
os.makedirs(outdir, exist_ok=True)
open(os.path.join(outdir, 'order.txt'), 'w').write('\n'.join(order) + '\n')
roots = sorted({r for m in order for r in mlroots.get(m, [])})
open(os.path.join(outdir, 'roots.txt'), 'w').write('\n'.join(roots) + '\n')

# a text-level sorry census: `sorry` tokens outside comments and strings, by declaration
decl_re = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                     r'(?:theorem|lemma|def|abbrev|instance|example|structure|inductive)\s+([^\s:({\[]+)?')


def strip_comments(t):
    out = []
    i = 0
    depth = 0
    n = len(t)
    while i < n:
        if t.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth and t.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth:
            out.append('\n' if t[i] == '\n' else ' ')
            i += 1
            continue
        if t.startswith('--', i):
            j = t.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
            continue
        if t[i] == '"':
            j = i + 1
            while j < n and t[j] != '"':
                j += 2 if t[j] == '\\' else 1
            out.append(' ' * (j + 1 - i))
            i = j + 1
            continue
        out.append(t[i])
        i += 1
    return ''.join(out)


census = []
total = 0
for m in order:
    t = strip_comments(src[m])
    names = []
    cur = None
    ns = []
    for line in t.split('\n'):
        s = line.strip()
        mm = re.match(r'^namespace\s+(\S+)', s)
        if mm:
            ns.append(mm.group(1))
        dm = decl_re.match(s)
        if dm and not line.startswith(' '):
            cur = dm.group(1)
        if re.search(r'(?<![\w.])sorry(?![\w])', line):
            if cur not in names:
                names.append(cur)
    if names:
        total += len(names)
        census.append(f"{m.replace('TCSlib/Complexity/', '')}: {len(names)}: {', '.join(names)}")
census.append(f'TOTAL {total}')
open(os.path.join(outdir, 'sorries-text.txt'), 'w').write('\n'.join(census) + '\n')
print(len(order), 'modules;', len(roots), 'roots;', total, 'sorry declarations (text);',
      len(missing), 'missing imports', missing)
