"""ctlmap.py <lean file> <elab output>: map each error to the control (doc comment) it falls in."""
import sys, re
src = open(sys.argv[1], encoding='utf-8').read().split('\n')
out = open(sys.argv[2], encoding='utf-8').read()
fn = sys.argv[1].split('/')[-1]
ctl_lines = {}  # line -> control label covering it
cur = None
for i, l in enumerate(src, 1):
    m = re.match(r'/-- (Control [^:]+):', l)
    if m: cur = (m.group(1), i)
    elif cur and (l.strip() == '' or l.startswith('/--') or l.startswith('end ')):
        if l.strip() == '': cur = None
    if cur: ctl_lines[i] = cur[0]
errs = [(int(m.group(1)), m.group(0)) for m in re.finditer(r'^\S*' + re.escape(fn) + r':(\d+):\d+: error', out, re.M)]
labels = sorted(set(v for v in ctl_lines.values()))
hit = {}
outside = []
for ln, e in errs:
    lab = ctl_lines.get(ln)
    if lab: hit.setdefault(lab, []).append(ln)
    else: outside.append(e)
print('errors', len(errs), '; controls', len(labels))
print('errors outside a control:', outside or 'none')
print('controls without an error:', [l for l in labels if l not in hit] or 'none')
print('controls with more than one error:', [l for l in hit if len(hit[l]) > 1] or 'none')
