"""Map each error of an elaboration output to the control (-- Cnn comment) whose example contains it.
Usage: ctlmap.py <probe.lean> <elab .out>"""
import re, sys
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
ctl = [(i + 1, l[3:].strip()) for i, l in enumerate(L) if re.match(r'-- C\d\d ', l)]
end = next(i + 1 for i, l in enumerate(L) if l.startswith('-- SEAL-CONTROLS-END'))
errs = [int(m.group(1)) for m in re.finditer(r':(\d+):\d+: error', open(sys.argv[2], encoding='utf-8').read())]
hit = {}
outside = []
for e in errs:
    owner = None
    for j, (ln, name) in enumerate(ctl):
        nxt = ctl[j + 1][0] if j + 1 < len(ctl) else end
        if ln < e < nxt: owner = name
    if owner is None: outside.append(e)
    else: hit.setdefault(owner, []).append(e)
print(f'controls {len(ctl)}; errors {len(errs)}; errors outside the controls: {outside}')
for ln, name in ctl: print(f'  {name:55s} {"FAILS (" + str(len(hit[name])) + " error)" if name in hit else "closes"}')
