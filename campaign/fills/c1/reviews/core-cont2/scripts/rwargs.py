"""Every identifier passed to rw/rwa/simp/simp only/simpa/dsimp/unfold/simp_rw/nth_rw/erw/conv rw
in the added lines of a unified diff (code only), classified as own-file, another file's definition
(from a KIND probe), another file's theorem, or other (local hypotheses/lets, Mathlib/core).
usage: rwargs.py <unified diff> <kinds out> <owned file>"""
import re, sys
added = [l[1:] for l in open(sys.argv[1], encoding='utf-8') if l.startswith('+') and not l.startswith('+++')]
src = '\n'.join(added)
out, i, depth = [], 0, 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
    out.append(src[i] if depth == 0 else (' ' if src[i] != '\n' else '\n')); i += 1
code = '\n'.join(l.split('--')[0] for l in ''.join(out).split('\n'))
kinds = {}
for l in open(sys.argv[2], encoding='utf-8'):
    m = re.search(r'KIND (\S+): (\w+); reducibility (\S+); projection (\w+); instance (\w+); matcher (\w+); simpUnfold (\w+); simpEq1 (\w+); module some \((\S+)\)', l)
    if m: kinds[m.group(1)] = m.groups()
own = set(re.findall(r'^(?:private\s+)?(?:theorem|def|instance|abbrev)\s+(\S+)', open(sys.argv[3], encoding='utf-8').read(), re.M))
args = []
# rewrite lists may span lines: join brackets
for m in re.finditer(r'\b(rw|rwa|simp only|simp|simpa only|simpa|dsimp only|dsimp|simp_rw|nth_rw \d+|erw|norm_num)\s*(\[[^\]]*\])', code, re.S):
    for a in re.split(r',(?![^\(\)]*\))', m.group(2)[1:-1]):
        a = a.strip(); a = re.sub(r'^←\s*', '', a)
        nm = re.match(r"[A-Za-z_↓][A-Za-z0-9_'.₀-₉ιℓ]*", a)
        if nm: args.append((m.group(1).split()[0], nm.group(0)))
for m in re.finditer(r'\bunfold\s+([^\n]+)', code):
    for a in m.group(1).split():
        if re.match(r"[A-Za-z_]", a) and a not in ('at',): args.append(('unfold', a))
uniq = sorted({a for _, a in args})
def cls(a):
    if a in own: return 'own-file declaration'
    for cand in (a, 'Turing.' + a, 'Turing.MultiTapeTM.' + a, 'Turing.NDTM.' + a, 'Turing.FinTM.' + a, 'Turing.Cfg.' + a, 'Turing.StepBlock.' + a):
        if cand in kinds:
            k = kinds[cand]
            if k[1] == 'def': return 'OTHER-FILE DEFINITION' + (' (projection)' if k[3] == 'true' else '')
            return 'TCSlib ' + k[1]
    return 'other (local hypothesis/let, Mathlib/core)'
res = {}
for a in uniq: res.setdefault(cls(a), []).append(a)
from collections import Counter
print('added code: rewrite/simp/unfold argument occurrences:', len(args), '; distinct identifiers:', len(uniq), '; by tactic:', dict(Counter(t for t, _ in args)))
for k in sorted(res): print(f'## {k}: {len(res[k])}\n   ' + ' '.join(res[k]))
