"""Compare a head declaration's code with a probe declaration's, after renaming (python3 -I).
usage: python3 -I transcmp.py <head> <decl> <probe> <probe decl> [old=new ...]"""
import re, sys, difflib
def get(path, name):
    L = open(path, encoding='utf-8').read().split('\n')
    i = next(k for k, l in enumerate(L) if re.match(r'^(private )?(theorem|def) ' + re.escape(name) + r'\b', l))
    j = i + 1
    while j < len(L) and L[j].strip() and not L[j].startswith('/--') and not re.match(r'^(private )?(theorem|def|end|section|#)', L[j]): j += 1
    return L[i:j]
a = get(sys.argv[1], sys.argv[2]); b = get(sys.argv[3], sys.argv[4])
for sub in sys.argv[5:]:
    o, n = sub.split('=', 1); b = [l.replace(o, n) for l in b]
a = [l.replace('private ', '', 1) if k == 0 else l for k, l in enumerate(a)]
print(f'{sys.argv[2]} ({len(a)} lines) vs {sys.argv[4]} ({len(b)} lines), renamed {sys.argv[5:]}: identical={a == b}')
for l in difflib.unified_diff(b, a, sys.argv[4], sys.argv[2], lineterm='', n=0): print('  ', l)
