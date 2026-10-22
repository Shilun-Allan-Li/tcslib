import sys, re
# usage: mentions.py <file> <defs...>: every comment-stripped code line naming a definition (whole identifier)
src = open(sys.argv[1], encoding='utf-8').read()
out, i, d = [], 0, 0
while i < len(src):
    if src.startswith('/-', i): d += 1; i += 2; continue
    if src.startswith('-/', i) and d > 0: d -= 1; i += 2; continue
    out.append(src[i] if d == 0 or src[i] == '\n' else ' '); i += 1
code = '\n'.join(l.split('--')[0] for l in ''.join(out).split('\n'))
for n, l in enumerate(code.split('\n'), 1):
    for dd in sys.argv[2:]:
        if re.search(r'(?<![\w.])' + re.escape(dd) + r'(?![\w\'])', l):
            print(f'{n:5} {dd:22} {l.strip()[:120]}')
