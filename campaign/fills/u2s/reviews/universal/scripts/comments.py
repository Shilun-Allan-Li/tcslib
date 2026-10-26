"""Extract comment/docstring text from a Lean source fragment. Usage: comments.py <file>"""
import sys
src = open(sys.argv[1], encoding='utf-8').read()
out = []; i = 0; depth = 0; cur = []
while i < len(src):
    if src.startswith('/-', i):
        depth += 1; i += 2; cur.append('/-'); continue
    if depth and src.startswith('-/', i):
        depth -= 1; i += 2; cur.append('-/')
        if depth == 0: out.append(''.join(cur)); cur = []
        continue
    if depth: cur.append(src[i]); i += 1; continue
    if src.startswith('--', i):
        j = src.find('\n', i); j = len(src) if j < 0 else j
        out.append(src[i:j]); i = j; continue
    i += 1
print('\n\n'.join(out))
