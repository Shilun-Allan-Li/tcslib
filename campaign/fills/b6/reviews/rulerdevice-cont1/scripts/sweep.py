"""Check a worker sweep log against the order list; map sorry warnings to declarations.
usage: sweep.py <log> <order list> <source tree root> [<other log>]"""
import sys, re, os
log, order, root = sys.argv[1], sys.argv[2], sys.argv[3]
other = sys.argv[4] if len(sys.argv) > 4 else None
mods = [l.strip() for l in open(order) if l.strip() and not l.startswith('#')]
def parse(p):
    runs = []; diags = []; cur = None
    for l in open(p, encoding='utf-8', errors='replace'):
        m = re.match(r'START (\d+)/(\d+) (\S+) ', l)
        if m: cur = m.group(3); continue
        m = re.match(r'END (\d+)/(\d+) (\S+) \S+ EXIT (\d+) WALL_SECONDS (\S+) MAX_RSS_KIB (\d+)', l)
        if m: runs.append((m.group(3), int(m.group(4)), float(m.group(5)), int(m.group(6)))); cur = None; continue
        m = re.match(r'^(TCSlib/\S+\.lean):(\d+):(\d+): (warning|error)(?:\([^)]*\))?: (.*)', l)
        if m: diags.append((m.group(1), int(m.group(2)), int(m.group(3)), m.group(4), m.group(5).strip()))
    return runs, diags
runs, diags = parse(log)
names = [r[0] for r in runs]
print('runs', len(runs), '; order list', len(mods), '; same sequence as the order list:', names == mods)
print('nonzero exits:', [r for r in runs if r[1] != 0] or 'none', '; error diagnostics:', len([d for d in diags if d[3] == 'error']))
print('max RSS KiB', max(r[3] for r in runs), '; summed wall s', round(sum(r[2] for r in runs), 3))
sor = [d for d in diags if d[3] == 'warning' and "declaration uses 'sorry'" in d[4]]
D = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(\S+)')
def declname(f, ln):
    L = open(os.path.join(root, f), encoding='utf-8').read().split('\n')
    m = D.match(L[ln-1].strip()) if ln-1 < len(L) else None
    return m.group(1) if m else '?' + L[ln-1][:40]
mapped = sorted((d[0].replace('TCSlib/Complexity/', '').replace('.lean', ''), declname(d[0], d[1])) for d in sor)
print('sorry warnings', len(sor), 'in', len({d[0] for d in sor}), 'modules')
for f, n in mapped: print('   ', f, ':', n)
if other:
    r2, d2 = parse(other)
    k = lambda d: (d[0], d[1], d[2], d[3], d[4])
    a = sorted(k(d) for d in diags if not d[0].endswith('Build/InputDevice.lean'))
    b = sorted(k(d) for d in d2 if not d[0].endswith('Build/InputDevice.lean'))
    print('diagnostics outside Build/InputDevice identical to the other log:', a == b, '(', len(a), 'vs', len(b), ')')
    print('Build/InputDevice diagnostics here:', [d for d in diags if d[0].endswith('Build/InputDevice.lean')])
    print('Build/InputDevice diagnostics in the other log:', [d for d in d2 if d[0].endswith('Build/InputDevice.lean')])
