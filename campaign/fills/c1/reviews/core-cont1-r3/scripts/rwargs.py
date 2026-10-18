"""Every identifier passed to rw/rwa/simp/simp only/simpa/dsimp/unfold/simp_rw/nth_rw/conv rw in a
Lean file (code only), classified as own-file, another file's definition (from a KIND probe), or
other (theorems, local hypotheses, Mathlib/core). usage: rwargs.py <file> <kinds out> <declnames>"""
import re, sys
src = open(sys.argv[1], encoding='utf-8').read()
out, i, depth = [], 0, 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
    out.append(src[i] if depth == 0 else (' ' if src[i] != '\n' else '\n')); i += 1
code = '\n'.join(l.split('--')[0] for l in ''.join(out).split('\n'))
kinds = {}
for l in open(sys.argv[2], encoding='utf-8'):
    m = re.search(r'KIND (\S+): (\w+); reducibility \S+; projection (\w+); instance (\w+); matcher (\w+)', l)
    if m: kinds[m.group(1)] = (m.group(2), m.group(3) == 'true')
own = {l.split()[1].replace('Turing.', '') for l in open(sys.argv[3], encoding='utf-8')}
args = []
for m in re.finditer(r'\b(rw|rwa|simp only|simp|simpa only|simpa|dsimp only|dsimp|simp_rw|nth_rw \d+|erw)\s*(\[[^\]]*\])', code):
    for a in re.split(r',(?![^\(\)]*\))', m.group(2)[1:-1]):
        a = a.strip()
        a = re.sub(r'^←\s*', '', a)
        nm = re.match(r"[A-Za-z_][A-Za-z0-9_'.₀-₉ιℓ]*", a)
        if nm: args.append((m.group(1), nm.group(0)))
for m in re.finditer(r'\bunfold\s+([^\n]+)', code):
    for a in m.group(1).split():
        if re.match(r"[A-Za-z_]", a) and a not in ('at',): args.append(('unfold', a))
uniq = sorted({a for _, a in args})
def cls(a):
    base = a.split('.')[-1] if a.startswith('xr_') else a
    if a in own or a.split('.')[0] in own: return 'own'
    for cand in (a, 'Turing.' + a, 'Turing.MultiTapeTM.' + a, 'Turing.NDTM.' + a, 'Turing.FinTM.' + a, 'Turing.Cfg.' + a):
        if cand in kinds: return 'TCSlib ' + kinds[cand][0] + (' (projection)' if kinds[cand][1] else '')
    return 'other'
res = {}
for a in uniq: res.setdefault(cls(a), []).append(a)
print('rewrite/simp/unfold argument occurrences:', len(args), '; distinct identifiers:', len(uniq))
for k in sorted(res): print(f'## {k}: {len(res[k])}\n   ' + ' '.join(res[k]))
