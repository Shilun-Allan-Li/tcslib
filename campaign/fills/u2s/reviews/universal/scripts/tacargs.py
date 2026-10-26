"""Collect the bracketed arguments of rw/rwa/simp/simp only/simpa/dsimp/unfold and the terms of show/change
in a Lean source fragment (the diff's added lines), joining continuation lines.
Usage: tacargs.py <added-lines file>"""
import re, sys
src = open(sys.argv[1], encoding='utf-8').read()
# strip comments
out = []; i = 0; depth = 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
    if depth: i += 1; continue
    if src.startswith('--', i):
        j = src.find('\n', i); i = len(src) if j < 0 else j; continue
    out.append(src[i]); i += 1
code = ''.join(out)
occ = []
for m in re.finditer(r'\b(rw|rwa|erw|simp only|simp|simpa only|simpa|dsimp only|dsimp|unfold|simp_rw|nth_rewrite|rewrite)\b(\s*\[)?', code):
    kind = m.group(1)
    if kind in ('unfold',):
        line = code[m.end():code.find('\n', m.end())]
        occ.append((kind, line.strip())); continue
    if not m.group(2):
        occ.append((kind, '(no lemma list)')); continue
    k = m.end(); d = 1; s = k
    while k < len(code) and d:
        if code[k] == '[': d += 1
        elif code[k] == ']': d -= 1
        k += 1
    occ.append((kind, ' '.join(code[s:k-1].split())))
for m in re.finditer(r'\b(show|change)\b\s+(.*)', code):
    occ.append((m.group(1), m.group(2).strip()))
idents = {}
for kind, args in occ:
    if kind in ('show', 'change'): continue
    for a in re.split(r',(?![^\(\[]*[\)\]])', args):
        a = a.strip()
        a = re.sub(r'^(←|<-|↓)\s*', '', a)
        mm = re.match(r"([A-Za-z_Ͱ-Ͽἀ-῿][\w.'₀-₉!?Ͱ-Ͽ]*)", a)
        if mm: idents.setdefault(mm.group(1), set()).add(kind)
print(f'{len(occ)} occurrences')
for kind, args in occ: print(f'  {kind:12s} [{args}]')
print(f'\n{len(idents)} distinct leading identifiers in rewrite/simp lists:')
for n in sorted(idents): print(f'  {n:45s} {",".join(sorted(idents[n]))}')
