"""Join the tactic-argument rows with their kinds (python3 -I).
usage: python3 -I classify.py <tacargs.tsv> <kinds .out>"""
import re, sys
from collections import defaultdict, Counter
rows = [l.rstrip('\n').split('\t') for l in open(sys.argv[1], encoding='utf-8') if l.strip()]
K = defaultdict(list)
for l in open(sys.argv[2], encoding='utf-8'):
    if l.startswith('KIND '):
        n, full, kind, mod = [x.strip() for x in l[5:].split('|')]
        K[n].append((full, kind, mod))
def cls(x):
    x = x.lstrip('←').strip()
    if x == '-' or x == '_' or re.search(r'\.[0-9]', x): return [('local', x, '-', '-')]
    out = []
    for full, kind, mod in K.get(x, [('-', 'local (not a global constant)', '-')]):
        if kind.startswith('local'): out.append(('local', x, '-', '-'))
        elif mod == 'this_module': out.append(('own', full, kind, mod))
        elif mod.startswith('TCSlib'): out.append(('tcslib', full, kind, mod))
        else: out.append(('core/mathlib', full, kind, mod))
    return out
ARGK = {'rw', 'rwa', 'simp', 'simp only', 'simpa', 'simpa only', 'dsimp', 'dsimp only', 'unfold', 'delta',
        'simp_all', 'simp_all only', 'simp_rw', 'nth_rw', 'norm_num', 'field_simp'}
tally = Counter(); findings = []; showdefs = defaultdict(set); distinct = defaultdict(set)
for k, x, ln in rows:
    for c, full, kind, mod in cls(x):
        cat = c
        if c in ('tcslib', 'core/mathlib'):
            cat = f'{c} {kind.split("[")[0]}'
        tally[(k if k in ARGK else k, cat)] += 1
        distinct[cat].add(full if c != 'local' else x)
        if k in ARGK and c in ('tcslib', 'core/mathlib') and kind.startswith('def'):
            findings.append((k, full, kind, mod, ln))
        if k in ARGK and c == 'tcslib' and kind == 'opaque':
            findings.append((k, full, kind, mod, ln))
        if k == 'show term' and c in ('tcslib', 'core/mathlib') and kind.startswith('def'):
            showdefs[(c, full, kind)].add(int(ln))
print('## rows by tactic kind and class')
for (k, cat), v in sorted(tally.items()): print(f'  {k:16s} {cat:28s} {v}')
print('## distinct identifiers per class')
for cat, s in sorted(distinct.items()): print(f'  {cat}: {len(s)}')
print('## definitions (or opaques) of other files or of core/Mathlib passed to rw/simp/dsimp/unfold:')
for f in findings: print('  ', f)
if not findings: print('   none')
print('## definitions named in show/change terms (other files and core/Mathlib), with their lines:')
for (c, full, kind), lns in sorted(showdefs.items()): print(f'   {c} {full} {kind}: {sorted(lns)}')
print('## other-file TCSlib theorems passed to rw/simp (distinct):')
print('  ', sorted({full for k, x, ln in rows if k in ARGK for c, full, kind, mod in cls(x) if c == 'tcslib' and kind == 'thm'}))
print('## other-file TCSlib non-theorem, non-definition names in rw/simp lists:')
print('  ', sorted({(full, kind) for k, x, ln in rows if k in ARGK for c, full, kind, mod in cls(x) if c == 'tcslib' and kind not in ('thm',) and not kind.startswith('def')}))
print('## core/Mathlib non-theorem names in rw/simp lists:')
print('  ', sorted({(full, kind) for k, x, ln in rows if k in ARGK for c, full, kind, mod in cls(x) if c == 'core/mathlib' and kind != 'thm'}))
