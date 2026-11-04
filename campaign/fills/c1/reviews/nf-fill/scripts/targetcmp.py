"""Compare the target's code (after its docstring) and docstring at base and head (python3 -I).
usage: python3 -I targetcmp.py <base> <head> <decl line prefix>"""
import sys, difflib
def split(path, key):
    L = open(path, encoding='utf-8').read().split('\n')
    i = next(k for k, l in enumerate(L) if l.startswith(key))
    j = i
    while not L[j].startswith('/--'): j -= 1
    e = i
    while e < len(L) and L[e].strip() != '': e += 1
    return L[j:i], L[i:e], (j + 1, i + 1, e)
for nm, p in (('base', sys.argv[1]), ('head', sys.argv[2])):
    d, c, pos = split(p, sys.argv[3]); print(f'{nm}: docstring lines {pos[0]}-{pos[1]-1}, code lines {pos[1]}-{pos[2]}')
db, cb, _ = split(sys.argv[1], sys.argv[3]); dh, ch, _ = split(sys.argv[2], sys.argv[3])
print('code (statement + body) byte-identical:', cb == ch)
for l in cb: print('   |', l)
print('## docstring diff')
for l in difflib.unified_diff(db, dh, 'base', 'head', lineterm='', n=0): print(l)
