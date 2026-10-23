"""Map the diagnostics of a seal run to its controls and to the body.
usage: ctlmap.py <seal .lean> <elab out> <offset of body lines (sealed line - original line)>"""
import re, sys
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
off = int(sys.argv[3])
ctl = []  # (start line, end line, label)
for i, l in enumerate(L):
    m = re.match(r'/-- Control (\S+): closes only (?:by unfolding|through the `@\[simp\]` unfolding of) `([^`]+)`', l)
    if m:
        j = i + 1
        while j < len(L) and L[j].strip(): j += 1
        ctl.append((i + 2, j, m.group(1), m.group(2)))
diag = []
for l in open(sys.argv[2], encoding='utf-8'):
    m = re.match(r'^\S+\.lean:(\d+):(\d+): (error|warning)', l)
    if m: diag.append((int(m.group(1)), m.group(3), l.strip()[:160]))
hit = {c[2]: [] for c in ctl}; body = []
for ln, kind, txt in diag:
    c = next((c for c in ctl if c[0] <= ln <= c[1]), None)
    if c: hit[c[2]].append(kind)
    else: body.append((ln, ln - off, kind, txt))
fail = [c[2] for c in ctl if 'error' in hit[c[2]]]; ok = [c[2] for c in ctl if 'error' not in hit[c[2]]]
print(f'controls: {len(ctl)}; failing (error): {len(fail)}; passing: {len(ok)}')
print('  passing controls:', ok)
print(f'diagnostics outside the controls: {len(body)}')
for ln, orig, kind, txt in body: print(f'  sealed line {ln} = original line {orig}: {kind}: {txt}')
