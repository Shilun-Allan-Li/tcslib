"""The cont5 regions table (read-only): every declaration of CodeSimulator.lean at the issue
tree, its line, docstring line, visibility, kind and region. Regions carry over from cont4's
table by name; the only new names must be cont4's 35 privates (PR #107).

Usage: python3 -I mkregions.py <base CodeSimulator.lean> <cont4 regions.tsv> <cont4 names> <out>
"""
import re, sys
base, old, names4, out = sys.argv[1:5]
L = open(base, encoding='utf-8').read().split('\n')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s(:{\[]+)')
depth, rows, doc = 0, [], None
for i, l in enumerate(L):
    start = depth
    j = 0
    while j < len(l):
        if l.startswith('/-', j): depth += 1; j += 2; continue
        if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
        if depth == 0 and l.startswith('--', j): break
        j += 1
    if start == 0 and l.startswith('/--'): doc = i + 1
    if start > 0: continue
    m = DECL.match(l)
    if m:
        vis = 'private' if 'private' in (m.group(1) or '') else 'public'
        rows.append((i + 1, doc if doc else '', vis, m.group(2), m.group(3))); doc = None
    elif l.strip() and not l.startswith('/--') and depth == 0 and not l.startswith(' '):
        doc = None if not l.rstrip().endswith('-/') else doc
reg = {}
for l in open(old, encoding='utf-8'):
    if l.startswith('#') or l.startswith('line\t'): continue
    f = l.rstrip('\n').split('\t'); reg[f[4]] = f[5]
new4 = [n for n in open(names4, encoding='utf-8').read().split() if n]
assert len(new4) == 35, len(new4)
names = [r[4] for r in rows]
assert len(names) == len(set(names)), 'duplicate names'
gone = sorted(set(reg) - set(names)); assert not gone, ('cont4 names missing', gone)
extra = sorted(set(names) - set(reg)); assert sorted(extra) == sorted(new4), (set(extra) ^ set(new4))
SPECIAL = {'exists_canonStripTM': 'canonizer: cont3 delivery (#96), frozen except the prescribed factoring edit',
           'canonPatchWord': 'canonizer: cont4 delivery (#107), frozen except the prescribed factoring edit'}
with open(out, 'w', encoding='utf-8') as o:
    o.write('# CodeSimulator.lean at the issue tree (campaign tip 64e8fe2b, Lean = 6354471a, after #107): every declaration, its line, its docstring line, visibility, kind and region\n')
    o.write('line\tdoc\tvisibility\tkind\tname\tregion\n')
    for (ln, d, vis, kind, n) in rows:
        r = SPECIAL.get(n) or reg.get(n) or 'canonizer: cont4 delivery (#107), frozen'
        o.write(f'{ln}\t{d}\t{vis}\t{kind}\t{n}\t{r}\n')
print(len(rows), 'declarations')
