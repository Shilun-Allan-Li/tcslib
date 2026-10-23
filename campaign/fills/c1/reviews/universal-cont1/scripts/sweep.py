"""sweep.py <order list> <base sorries> <bootstrap log> <final log>: order, completeness, errors,
sorry warnings per module vs the base set, and every non-owned diagnostic bootstrap vs final."""
import sys, re
order = [l.strip() for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
base = {}
for l in open(sys.argv[2]):
    m = re.match(r'^(\S+): (\d+):', l)
    if m: base['TCSlib/Complexity/' + m.group(1)] = int(m.group(2))
def parse(p):
    mods, cur, diag, starts = [], None, {}, {}
    for l in open(p, encoding='utf-8', errors='replace'):
        m = re.match(r'^=== (\S+) start (\S+)', l)
        if m: cur = m.group(1); mods.append(cur); starts[cur] = m.group(2); diag[cur] = []; continue
        m = re.match(r'^=== (\S+) end', l)
        if m: cur = None; continue
        m = re.match(r'^(\S+\.lean):(\d+):(\d+): (warning|error): (.*)$', l.rstrip())
        if m and cur: diag[cur].append((m.group(1), int(m.group(2)), int(m.group(3)), m.group(4), m.group(5)))
    return mods, diag, starts
for name, p in (('bootstrap', sys.argv[3]), ('final', sys.argv[4])):
    mods, diag, starts = parse(p)
    errs = sum(1 for m in diag for d in diag[m] if d[3] == 'error')
    sorr = {m: sum(1 for d in diag[m] if 'declaration uses' in d[4] and 'sorry' in d[4]) for m in diag}
    sorr = {m: v for m, v in sorr.items() if v}
    print(f'== {name}: {len(mods)} modules; in the order list\'s exact order: {mods == order}; errors {errs}; '
          f'sorry warnings {sum(sorr.values())} in {len(sorr)} modules')
    dif = {m: (base.get(m, 0), sorr.get(m, 0)) for m in set(base) | set(sorr) if base.get(m, 0) != sorr.get(m, 0)}
    print('   differs from the base set (base, here):', dif or 'none')
    if name == 'bootstrap': B = diag
    else: Fd = diag; print('   NTimeHierarchy checked at', starts.get('TCSlib/Complexity/Diagonalization/NTimeHierarchy'))
own = 'TCSlib/Complexity/Diagonalization/NTimeHierarchy'
same = all(B.get(m) == Fd.get(m) for m in set(B) | set(Fd) if m != own)
nd = sum(len(B[m]) for m in B if m != own)
print(f'non-owned diagnostics bootstrap vs final identical (file, line, col, kind, text): {same} ({nd} diagnostics)')
print('owned module, bootstrap:', [(d[1], d[3], d[4][:40]) for d in B[own]])
print('owned module, final:', [(d[1], d[3], d[4][:40]) for d in Fd[own]])
