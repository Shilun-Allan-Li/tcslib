"""Tactic-argument identifiers of head lines [a, b] (comments stripped), python3 -I.
Lists, per tactic kind, every identifier in the bracketed lists of rw/simp/simpa/dsimp/simp only/
unfold/rwa and every identifier in show/change/convert/apply/exact/refine/obtain/have terms.
usage: python3 -I tacargs.py <file> <a> <b> <out ids file>"""
import re, sys
f, a, b, outp = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
L = open(f, encoding='utf-8').read().split('\n')
src = '\n'.join(L[a - 1:b])
out, i, depth = [], 0, 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if src.startswith('-/', i) and depth: depth -= 1; i += 2; continue
    if not depth and src.startswith('--', i):
        j = src.find('\n', i); i = len(src) if j < 0 else j; continue
    if not depth: out.append(src[i])
    i += 1
code = ''.join(out)
ID = re.compile(r"(?<![\w.'])(?:←\s*)?([A-Za-z_][\w.'₀-₉]*)")
lists = {}
for m in re.finditer(r'\b(rw|rwa|simp only|simp|simpa only|simpa|dsimp only|dsimp|unfold|simp_rw|nth_rw)\b\s*(\[[^\]]*\])?', code):
    kind = m.group(1)
    if m.group(2):
        for x in ID.findall(m.group(2)): lists.setdefault(kind, []).append(x)
    elif kind == 'unfold':
        lists.setdefault(kind, []).append(code[m.end():].split('\n')[0].strip())
    else: lists.setdefault(kind + ' (no list)', []).append('-')
for m in re.finditer(r'\b(show|change|convert|apply|exact|refine|obtain|have|calc|by_cases|cases|rcases|rintro|intro|subst|using)\b([^\n]*)', code):
    for x in ID.findall(m.group(2)): lists.setdefault(m.group(1) + ' term', []).append(x)
kw = {'fun', 'by', 'at', 'with', 'using', 'if', 'then', 'else', 'this', 'only', 'in', 'from', 'let'}
ids = set()
for k, v in lists.items():
    v2 = [x for x in v if x not in kw]
    print(f'{k}: {len(v2)} occurrences: {sorted(set(v2))}')
    ids |= {x for x in v2 if x != '-'}
open(outp, 'w', encoding='utf-8').write('\n'.join(sorted(ids)) + '\n')
print(f'distinct identifiers: {len(ids)}')
