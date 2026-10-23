#!/usr/bin/env python3
"""usage: hygiene.py <head file> <ranges a-b,...>: keyword, width and whitespace hygiene of the
owned region (code with comments stripped for the keyword scan)."""
import re, sys
src, ranges = sys.argv[1], sys.argv[2]
L = open(src, encoding='utf-8').read().split('\n')
keep = []
for r in ranges.split(','):
    a, b = map(int, r.split('-')); keep += list(range(a, b + 1))
text = '\n'.join(L); out = []; i = 0; depth = 0
while i < len(text):
    if text.startswith('/-', i): depth += 1; i += 2; out.append('  '); continue
    if text.startswith('-/', i) and depth > 0: depth -= 1; i += 2; out.append('  '); continue
    if depth == 0 and text.startswith('--', i):
        j = text.find('\n', i); j = len(text) if j < 0 else j; out.append(' ' * (j - i)); i = j; continue
    out.append(text[i] if depth == 0 or text[i] == '\n' else ' '); i += 1
code = ''.join(out).split('\n')
KW = ['sorry', 'admit', 'axiom', 'set_option', 'open', 'section', 'namespace', 'end', 'variable',
      'attribute', 'native_decide', 'decide', 'instance', 'deriving', 'unfold', 'delta',
      'noncomputable', 'macro', 'elab', 'syntax', 'simp_all', 'aesop', 'norm_num', 'omega', 'nlinarith',
      'ring', 'rfl', 'show', 'change', 'exact?', 'apply?', 'classical', 'Classical', 'by_contra', 'decreasing_by', 'termination_by']
cnt = {}
hits = {}
for n in keep:
    for k in KW:
        if re.search(r'(?<![\w.@])' + re.escape(k) + r'(?![\w?!\'])', code[n - 1]):
            cnt[k] = cnt.get(k, 0) + 1
            hits.setdefault(k, []).append(n)
print('keyword lines (code only):', ', '.join(f'{k} {cnt[k]}' for k in KW if k in cnt))
for k in ('sorry', 'admit', 'axiom', 'set_option', 'open', 'section', 'namespace', 'end', 'variable', 'attribute',
          'native_decide', 'decide', 'instance', 'deriving', 'unfold', 'delta', 'noncomputable', 'macro', 'elab', 'syntax',
          'simp_all', 'aesop', 'norm_num', 'decreasing_by', 'termination_by'):
    if k in hits: print(f'  {k}: lines {hits[k][:20]}')
print('# command lines:', [n for n in keep if code[n - 1].lstrip().startswith('#')])
w = [(n, len(L[n - 1])) for n in keep if len(L[n - 1]) > 100]
print('lines over 100 chars in region:', w, '| widest:', max(len(L[n - 1]) for n in keep))
print('whole file over 100:', [(i + 1, len(l)) for i, l in enumerate(L) if len(l) > 100])
print('trailing whitespace:', [n for n in keep if L[n - 1] != L[n - 1].rstrip()][:20])
print('tabs:', [n for n in keep if '\t' in L[n - 1]][:20])
dbl = [n for n in keep if n > 1 and L[n - 1].strip() == '' and L[n - 2].strip() == '']
print('double blank lines (second blank):', dbl)
