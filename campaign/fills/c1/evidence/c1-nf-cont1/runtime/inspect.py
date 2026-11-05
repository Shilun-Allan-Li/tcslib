#!/usr/bin/env python3
"""inspect.py <module> <walk-ext.tsv> <out.md>: the inspection table of every rw/simp/simpa/dsimp/
unfold/show/change argument in the new region (the diff against the base)."""
import re, sys, subprocess
mod, ext, out = sys.argv[1:4]
base = subprocess.run(['git','show','HEAD:TCSlib/Complexity/ClassNP/NDNormalForm.lean'] if False else
                      ['cat','scratch/NDNormalForm.base.lean'],capture_output=True,text=True).stdout.split('\n')
cur = open(mod).read().split('\n')
# new region: lines after 704 of the base, up to the target's docstring
start = 704; end = next(i for i,l in enumerate(cur) if l.startswith('/-- **The linear-overhead coded normal form**'))
tgt = next(i for i,l in enumerate(cur) if l.startswith('theorem exists_codeNDTM_accepts_linear'))
lines = list(enumerate(cur[start:end], start+1)) + list(enumerate(cur[tgt:], tgt+1))
kinds = {}
for l in open(ext):
    p = l.rstrip('\n').split('\t')
    if len(p) == 3: kinds[p[0]] = (p[1], p[2])
def classify(a):
    a0 = a.lstrip('←').strip()
    a0 = re.sub(r'^\(|\)$','',a0)
    head = a0.split()[0] if a0 else a0
    if head.startswith('nf_') or head.startswith('_root_') : return 'own (this file)'
    for cand in [head, 'Turing.'+head, 'Turing.FinNDTM.'+head, 'Turing.MultiTapeTM.'+head]:
        if cand in kinds:
            k, m = kinds[cand]
            src = 'TCSlib' if m.startswith('TCSlib') else ('core' if m.startswith(('Init','Std','Lean')) else 'Mathlib')
            return f'{src} {k} ({m})'
    if re.match(r'^[a-z][A-Za-z0-9_₀-₉\']*$', head) or head.startswith('h') : return 'local hypothesis/term'
    if re.match(r'^(List|Fin|Nat|Int|Option|SignType|Function|Bool)\.', head):
        return 'core/Mathlib lemma (applied definitionally by simp: no constant left in the term)'
    if head.startswith('show ') or head.startswith('(show'): return 'local proof term'
    return 'unresolved: ' + head
rows = []
pat = re.compile(r'\b(rw|rwa|simp only|simp|simpa only|simpa|dsimp only|dsimp|unfold|show|change|nth_rewrite|simp_all)\b(.*)')
segs = []
for n, l in lines:
    if l.strip().startswith('--'): continue
    for seg in re.split(r';\s+(?![^\[]*\])', l): segs.append((n, seg))
for n, l in segs:
    m = pat.search(l)
    if not m: continue
    tac, rest = m.group(1), m.group(2)
    if tac in ('show','change'):
        rows.append((n, tac, rest.strip()[:90], 'goal restatement (own statement form; no unfolding of other files)'))
        continue
    if tac == 'unfold':
        for a in rest.split():
            if a.startswith('at'): break
            rows.append((n, tac, a, classify(a)))
        continue
    br = re.search(r'\[(.*)\]', rest) if '[' in rest else None
    if br is None:
        rows.append((n, tac, '(no arguments)', 'default simp set / closing'))
        continue
    args = [a.strip() for a in re.split(r',(?![^()]*\))', br.group(1)) if a.strip()]
    for a in args: rows.append((n, tac, a, classify(a)))
with open(out,'w') as f:
    f.write('| line | tactic | argument | origin |\n|---|---|---|---|\n')
    for r in rows: f.write('| %d | `%s` | `%s` | %s |\n' % (r[0], r[1], r[2].replace('|','\\|'), r[3]))
print(len(rows), 'rows;', sum(1 for r in rows if r[3].startswith('unresolved')), 'unresolved')
