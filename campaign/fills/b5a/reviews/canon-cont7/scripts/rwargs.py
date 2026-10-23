#!/usr/bin/env python3
"""Inventory of rewrite/simp/unfold/show/change arguments in the owned region.

usage: rwargs.py <head file> <ranges like 4953-7576,7604-8074> <out json> <out txt>
Comments and docstrings are stripped first. For every `rw`, `rwa`, `erw`, `rw_mod_cast`,
`simp`, `simp only`, `simp_all`, `simpa`, `dsimp`, `dsimp only`, `simp_rw`, `norm_num`,
`field_simp`, `unfold`, `delta`, `conv` occurrence, the bracketed argument list is parsed into
identifiers (a leading `←` and term arguments are kept as written; the identifier is the first
dotted name of each argument). `show`/`change` lines are listed verbatim with line numbers.
"""
import json, re, sys
src, ranges, outj, outt = sys.argv[1:5]
lines = open(src, encoding='utf-8').read().split('\n')
keep = set()
for r in ranges.split(','):
    a, b = map(int, r.split('-'))
    keep.update(range(a, b + 1))
# strip comments while preserving line structure
text = '\n'.join(lines)
out, i, depth = [], 0, 0
while i < len(text):
    if text.startswith('/-', i):
        depth += 1; i += 2; continue
    if text.startswith('-/', i) and depth > 0:
        depth -= 1; i += 2; continue
    if depth == 0 and text.startswith('--', i):
        j = text.find('\n', i)
        i = j if j >= 0 else len(text)
        continue
    ch = text[i]
    out.append(ch if depth == 0 or ch == '\n' else ' ')
    i += 1
code = ''.join(out).split('\n')
assert len(code) == len(lines)
# region text with line map
pos2line = []
region = ''
for n in sorted(keep):
    l = code[n - 1]
    for _ in l + '\n':
        pos2line.append(n)
    region += l + '\n'
TAC = re.compile(r'(?<![\w.])(rw_mod_cast|rwa|erw|rw|simp_rw|simp_all only|simp_all|simpa only|simpa|'
                 r'simp only|simp|dsimp only|dsimp|norm_num|field_simp|unfold|delta|conv)(?![\w.])')
def args_after(k):
    # skip spaces and options like (config := ...) / `at`? find '[' before newline-dedent
    j = k
    while j < len(region) and region[j] in ' \t':
        j += 1
    if region.startswith('[', j):
        d, s = 0, j
        while j < len(region):
            if region[j] in '[(⟨{':
                d += 1
            elif region[j] in '])⟩}':
                d -= 1
                if d == 0:
                    return region[s + 1:j], s
            j += 1
    return None, j
def split_top(s):
    parts, d, cur = [], 0, ''
    for ch in s:
        if ch in '([⟨{':
            d += 1
        elif ch in ')]⟩}':
            d -= 1
        if ch == ',' and d == 0:
            parts.append(cur); cur = ''
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    return [' '.join(p.split()) for p in parts]
NAME = re.compile(r'^(←\s*|<-\s*|↓|-)?\s*@?([A-Za-z_À-ɏͰ-Ͽᴀ-ᶿ⁰-₟][\w\'.!?₀-₉ₐ-ₜͰ-Ͽ]*)')
records = []
for m in TAC.finditer(region):
    tac = m.group(1)
    line = pos2line[m.start()]
    if tac in ('unfold', 'delta'):
        rest = region[m.end():region.find('\n', m.end())]
        records.append({'line': line, 'tac': tac, 'args': rest.split(), 'raw': rest.strip()})
        continue
    a, _ = args_after(m.end())
    if a is None:
        records.append({'line': line, 'tac': tac, 'args': [], 'raw': ''})
        continue
    parts = split_top(a)
    records.append({'line': line, 'tac': tac, 'args': parts, 'raw': a})
idents = {}
for r in records:
    for p in r['args']:
        mm = NAME.match(p)
        if mm:
            idents.setdefault(mm.group(2), []).append(r['line'])
        else:
            idents.setdefault('<term> ' + p[:60], []).append(r['line'])
shows = [(n, code[n - 1].strip()) for n in sorted(keep)
         if re.search(r'(?<![\w.])(show|change)(?![\w.])', code[n - 1])]
unfolds = [r for r in records if r['tac'] in ('unfold', 'delta')]
bare = [r for r in records if r['tac'] in ('simp', 'simpa', 'simp_all', 'dsimp', 'norm_num', 'field_simp')]
json.dump({'idents': idents, 'records': records}, open(outj, 'w'), indent=0)
with open(outt, 'w', encoding='utf-8') as f:
    f.write(f'occurrences {len(records)}; distinct argument heads {len(idents)}\n')
    from collections import Counter
    c = Counter(r['tac'] for r in records)
    f.write('by tactic: ' + ', '.join(f'{k} {v}' for k, v in sorted(c.items())) + '\n')
    f.write(f'unfold/delta: {len(unfolds)}\n')
    for r in unfolds:
        f.write(f'  {r["line"]}: {r["tac"]} {r["raw"]}\n')
    f.write(f'non-only simp-family calls (default simp set): {len(bare)}\n')
    for r in bare:
        f.write(f'  {r["line"]}: {r["tac"]} [{r["raw"][:150]}]\n')
    f.write(f'show/change lines: {len(shows)}\n')
    for n, l in shows:
        f.write(f'  {n}: {l[:160]}\n')
    f.write('argument heads (first line of use):\n')
    for k in sorted(idents):
        f.write(f'  {k}  x{len(idents[k])}  first {idents[k][0]}\n')
print(f'occurrences {len(records)}; heads {len(idents)}; show/change {len(shows)}; unfold {len(unfolds)}')
