"""Hunks of base -> head (base line numbers), widths and hygiene of the added lines (python3 -I).
usage: python3 -I regions.py <base file> <head file>"""
import difflib, re, sys
A = open(sys.argv[1], encoding='utf-8').read().split('\n'); B = open(sys.argv[2], encoding='utf-8').read().split('\n')
sm = difflib.SequenceMatcher(a=A, b=B, autojunk=False)
added = []
print('## hunks (base lines a1-a2 -> head lines b1-b2)')
for tag, a1, a2, b1, b2 in sm.get_opcodes():
    if tag == 'equal': continue
    print(f'{tag}: base {a1+1}-{a2} ({a2-a1} lines) -> head {b1+1}-{b2} ({b2-b1} lines)')
    for l in A[a1:a2]: print('   -', l)
    for i in range(b1, b2):
        added.append((i + 1, B[i]))
        if b2 - b1 <= 12: print('   +', B[i])
print(f'## added lines: {len(added)}; widest (characters): {max(len(l) for _, l in added)}')
over = [(n, len(l)) for n, l in added if len(l) > 100]
print('added lines over 100 characters:', over)
print('whole-file lines over 100 characters, base:', sum(len(l) > 100 for l in A), '; head:', sum(len(l) > 100 for l in B))
code = []
depth = 0
for n, l in added:
    s = ''; j = 0
    while j < len(l):
        if l.startswith('/-', j): depth += 1; j += 2; continue
        if l.startswith('-/', j) and depth: depth -= 1; j += 2; continue
        if not depth and l.startswith('--', j): break
        if not depth: s += l[j]
        j += 1
    if s.strip(): code.append((n, s))
print(f'## added code lines (comments and docstrings stripped): {len(code)}')
for tok in ['sorry', 'admit', 'axiom', 'unfold', 'delta', 'set_option', 'open', 'section', 'variable',
            'attribute', 'instance', 'native_decide', 'simp_all', 'aesop', 'norm_num', 'decide', 'rfl',
            'show', 'change', 'convert', 'nlinarith', 'omega', 'Classical', 'noncomputable', 'def']:
    hits = [n for n, s in code if re.search(r'(?<![A-Za-z0-9_.])' + tok + r'(?![A-Za-z0-9_])', s)]
    if hits: print(f'  {tok}: {len(hits)} lines {hits}')
unres = [(n, s.strip()) for n, s in code if re.search(r'\bsimpa?\b(?!\s+only)(?!\?)', s)]
print('unrestricted simp/simpa:', unres)
blank_runs = [n for (n, l), (m, k) in zip(added, added[1:]) if not l.strip() and not k.strip() and m == n + 1]
print('consecutive blank added lines at head lines:', blank_runs)
