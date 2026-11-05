# tacargs.py <head file> <first line> <last line> <out.tsv> <idents.txt>
# Every rw/rwa/erw/simp/simp only/simpa/simp_all/dsimp/unfold/delta/show/change/norm_num/push_cast/
# field_simp argument in the line range (1-based, inclusive), with its line, tactic and identifiers.
import re, sys
f, a, b, out, idf = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
L = open(f, encoding='utf-8').read().split('\n')
# strip comments and docstrings, keep line numbers
code = []; depth = 0
for i, l in enumerate(L):
    o = ''; j = 0
    while j < len(l):
        if l.startswith('/-', j): depth += 1; j += 2; continue
        if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
        if depth == 0 and l.startswith('--', j): break
        if depth == 0: o += l[j]
        j += 1
    code.append(o)
text = '\n'.join(code)
# offsets of lines
offs = [0]
for l in code: offs.append(offs[-1] + len(l) + 1)
def lineof(p):
    lo, hi = 0, len(offs) - 1
    while lo < hi:
        m = (lo + hi + 1) // 2
        if offs[m] <= p: lo = m
        else: hi = m - 1
    return lo + 1
ID = re.compile(r"[^\W\d][\w'!?₀-₉ᵢ-ᵪ\.]*")
KW = {'by','fun','show','from','at','with','using','only','if','then','else','match','let','have','this',
      'at','in','do','λ','Type','Prop','Sort','true','false'}
TAC = re.compile(r'\b(rw|rwa|erw|rewrite|simp_all|simpa|simp|dsimp|norm_num|push_cast|field_simp|unfold|delta|show|change)\b(\??)(\s+only)?')
rows = []
def bracket(p):
    # p at '[' ; return content and end
    d = 0; q = p
    while q < len(text):
        c = text[q]
        if c in '[(⟨{': d += 1
        elif c in '])⟩}': d -= 1
        if d == 0: return text[p + 1:q], q
        q += 1
    return text[p + 1:], len(text)
def split_items(s):
    items = []; d = 0; cur = ''
    for c in s:
        if c in '[(⟨{': d += 1
        elif c in '])⟩}': d -= 1
        if c == ',' and d == 0: items.append(cur); cur = ''
        else: cur += c
    if cur.strip(): items.append(cur)
    return [x.strip() for x in items]
for m in TAC.finditer(text):
    ln = lineof(m.start())
    if ln < a or ln > b: continue
    tac = m.group(1) + (m.group(2) or '') + (' only' if m.group(3) else '')
    p = m.end()
    rest = text[p:p + 400]
    if tac.split()[0] in ('unfold', 'delta'):
        seg = rest.split('\n')[0]
        names = [x for x in seg.split() if ID.fullmatch(x)]
        for n in names: rows.append((ln, tac, n, n))
        continue
    if tac.split()[0] in ('show', 'change'):
        # the term up to ' from ', ':=' or end of line(s) at the same indentation; take the line
        seg = rest.split(' from ')[0].split('\n')[0]
        ids = [x for x in ID.findall(seg) if x not in KW]
        rows.append((ln, tac, seg.strip()[:80], ' '.join(ids)))
        continue
    k = p
    while k < len(text) and text[k] in ' \t': k += 1
    if k < len(text) and text[k] == '[':
        content, _ = bracket(k)
        for it in split_items(content):
            ids = [x for x in ID.findall(it.replace('←', ' ').replace('<-', ' ')) if x not in KW]
            rows.append((ln, tac, it.replace('\n', ' ')[:80], ' '.join(ids)))
    else:
        rows.append((ln, tac, '(no list)', ''))
with open(out, 'w', encoding='utf-8') as o:
    o.write('line\ttactic\targument\tidentifiers\n')
    for r in rows: o.write('\t'.join(map(str, r)) + '\n')
ids = sorted({x for r in rows for x in r[3].split() if x})
open(idf, 'w', encoding='utf-8').write('\n'.join(ids) + '\n')
print('rows', len(rows), 'identifiers', len(ids))
from collections import Counter
print(Counter(r[1] for r in rows))
