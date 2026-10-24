import re, sys
# usage: sealcheck.py <sealed .lean> <elab output> : map each error to the control (example) containing it
src = open(sys.argv[1], encoding='utf-8').read().split('\n')
ctl = []  # (start line, end line, name)
for i, l in enumerate(src, 1):
    m = re.match(r'/-- Control (\d+): closes only by unfolding `([^`]+)`', l)
    if m: ctl.append([i, None, m.group(2)])
for j in range(len(ctl)):
    nxt = ctl[j + 1][0] - 1 if j + 1 < len(ctl) else None
    if nxt is None:
        k = ctl[j][0]
        while src[k].strip(): k += 1
        nxt = k
    ctl[j][1] = nxt
errs = [int(m.group(1)) for m in re.finditer(r'\.lean:(\d+):\d+: error', open(sys.argv[2], encoding='utf-8').read())]
hit = {c[2]: 0 for c in ctl}; outside = []
for e in errs:
    for s, t, n in ctl:
        if s <= e <= t: hit[n] += 1; break
    else: outside.append(e)
print(f'controls {len(ctl)}; errors {len(errs)}; errors outside the controls: {outside}')
print('controls with != 1 error:', {n: h for n, h in hit.items() if h != 1})
