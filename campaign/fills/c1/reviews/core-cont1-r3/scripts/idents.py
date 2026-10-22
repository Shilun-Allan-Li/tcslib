"""Identifiers in the code (comments and docstrings stripped) of lines a..b of a Lean file.
usage: python3 -I idents.py <file> <a> <b>"""
import re, sys
src = open(sys.argv[1], encoding='utf-8').read().split('\n')
a, b = int(sys.argv[2]), int(sys.argv[3])
text = '\n'.join(src[a - 1:b])
out, i, depth = [], 0, 0
while i < len(text):
    if text.startswith('/-', i): depth += 1; i += 2; continue
    if text.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
    out.append(text[i] if depth == 0 else (' ' if text[i] != '\n' else '\n')); i += 1
code = '\n'.join(l.split('--')[0] for l in ''.join(out).split('\n'))
ids = sorted(set(re.findall(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_'₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'₀-₉]*)*)", code)))
print('\n'.join(ids))
