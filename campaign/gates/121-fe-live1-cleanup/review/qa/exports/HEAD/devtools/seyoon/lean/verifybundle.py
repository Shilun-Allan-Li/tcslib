import sys, re
# usage: verifybundle.py <root> <bundle> <listfile>: every listed file appears once, in order, with exact content
root, bundle, lst = sys.argv[1], sys.argv[2], sys.argv[3]
paths = [l.strip() for l in open(lst) if l.strip()]
b = open(bundle, encoding='utf-8').read()
hdr = re.compile(r'^## ===== (.+?) =====\n\n', re.M)
ms = list(hdr.finditer(b))
segs = []
for i, m in enumerate(ms):
    end = ms[i+1].start() - 1 if i + 1 < len(ms) else len(b)
    segs.append((m.group(1), b[m.end():end]))
names = [s[0] for s in segs]
bad = 0
if names != paths: print('ORDER/SET MISMATCH', len(names), len(paths)); bad += 1
for (p, c) in segs:
    t = open(f'{root}/{p}', encoding='utf-8').read(); t = t + ('' if t.endswith('\n') else '\n')
    if p.endswith('.lean') or p.endswith('.py'): t = '```\n' + t + '```\n'
    if c != t: print('CONTENT MISMATCH', p); bad += 1
print(f'{bundle}: {len(segs)} segments, {bad} problems')
