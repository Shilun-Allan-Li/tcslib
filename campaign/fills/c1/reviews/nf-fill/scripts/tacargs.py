"""Tactic-argument identifiers of head lines [a, b] (comments stripped), as (kind, identifier,
line) rows (python3 -I).  Bracketed lists of rw/rwa/simp/simp only/simpa/simpa only/dsimp/
dsimp only/simp_rw/nth_rw/simp_all/norm_num/field_simp (nested brackets balanced), unfold/delta
targets, and every identifier in show/change terms (to the end of the line).
usage: python3 -I tacargs2.py <file> <a> <b> <out tsv> <out ids>"""
import re, sys
f, a, b, outp, idsp = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
L = open(f, encoding='utf-8').read().split('\n')
# strip comments, keeping newlines (to keep line numbers)
src = '\n'.join(L[a - 1:b]); out, i, depth = [], 0, 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if src.startswith('-/', i) and depth: depth -= 1; i += 2; continue
    if not depth and src.startswith('--', i):
        j = src.find('\n', i); i = len(src) if j < 0 else j; continue
    out.append(src[i] if not depth or src[i] == '\n' else ' '); i += 1
code = ''.join(out)
def line_of(pos): return a + code.count('\n', 0, pos)
ID = re.compile(r"(?<![\w.'₀-₉])(?:←\s*)?([A-Za-z_][\w.'₀-₉!?]*)")
KW = {'fun', 'by', 'at', 'with', 'using', 'if', 'then', 'else', 'this', 'only', 'in', 'from', 'let',
      'show', 'have', 'exact', 'rfl', 'decide', 'omega', 'simp', 'Type', 'Prop', 'true', 'false',
      'match', 'do', 'return', 'calc', 'and', 'or', 'not', 'at', 'if', 'h'}
rows = []
TAC = re.compile(r'\b(rwa|rw|simp_rw|nth_rw\s+\d+|simpa only|simpa|simp_all only|simp_all|simp only|simp|dsimp only|dsimp|norm_num|field_simp)\b(\s*\[)?')
for m in TAC.finditer(code):
    kind = re.sub(r'\s+\d+', '', m.group(1))
    if not m.group(2):
        rows.append((kind + ' (no list)', '-', line_of(m.start()))); continue
    j = m.end(); d = 1
    while j < len(code) and d:
        if code[j] == '[': d += 1
        elif code[j] == ']': d -= 1
        j += 1
    lst = code[m.end():j - 1]
    for x in ID.finditer(lst):
        if x.group(1) not in KW: rows.append((kind, x.group(1), line_of(m.end() + x.start())))
for m in re.finditer(r'\b(unfold|delta)\b([^\n;)⟩]*)', code):
    for x in ID.finditer(m.group(2)):
        if x.group(1) not in KW: rows.append((m.group(1), x.group(1), line_of(m.start())))
for m in re.finditer(r'\b(show|change)\b([^\n]*)', code):
    for x in ID.finditer(m.group(2)):
        if x.group(1) not in KW: rows.append((m.group(1) + ' term', x.group(1), line_of(m.start())))
with open(outp, 'w', encoding='utf-8') as o:
    for k, x, ln in rows: o.write(f'{k}\t{x}\t{ln}\n')
ids = sorted({x for _, x, _ in rows if x != '-'})
open(idsp, 'w', encoding='utf-8').write('\n'.join(ids) + '\n')
from collections import Counter
c = Counter(k for k, _, _ in rows)
print('rows', len(rows), 'distinct identifiers', len(ids))
for k, v in sorted(c.items()): print(f'  {k}: {v}')
