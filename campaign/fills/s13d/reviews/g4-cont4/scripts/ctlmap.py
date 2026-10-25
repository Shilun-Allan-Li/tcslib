import sys, re
# usage: ctlmap.py <lean file> <lean output>
src = open(sys.argv[1], encoding='utf-8').read().split('\n')
starts = []  # (line, label)
for i, l in enumerate(src, 1):
    m = re.match(r'/-- Control (\d+): closes only by unfolding `([^`]+)`', l) or re.match(r'/-- Control (\d+): (the default simp set)', l)
    if m: starts.append((i, m.group(1) + ' ' + m.group(2)))
    m2 = re.match(r'^section S(\d+)$', l)
    if m2: starts.append((i, 'S' + m2.group(1) + ' ' + src[i].split()[-1]))
starts.sort()
out = open(sys.argv[2], encoding='utf-8').read()
errs = [int(m.group(1)) for m in re.finditer(r'^\S+?:(\d+):\d+: error', out, re.M)]
hit = {}
for e in errs:
    lab = None
    for ln, lb in starts:
        if ln <= e: lab = lb
        else: break
    hit.setdefault(lab, []).append(e)
labels = [lb for _, lb in starts]
print('controls', len(labels), '; errors', len(errs))
print('controls with no error:', [lb for lb in labels if lb not in hit])
print('controls with more than one error:', {k: v for k, v in hit.items() if len(v) > 1})
print('errors outside controls:', hit.get(None))
