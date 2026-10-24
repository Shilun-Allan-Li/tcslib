"""sweep.py <order list> <base sorries> <base worktree> <final sweep log> <bootstrap log>... :
module order, rc, errors, sorry warnings per module (mapped to declarations at the base), and diagnostics outside
WindowClock compared between the bootstrap and the final sweep."""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decls import decls
order = [l.strip() for l in open(sys.argv[1], encoding='utf-8') if l.strip()]
base = {}
for l in open(sys.argv[2], encoding='utf-8'):
    m = re.match(r'^(\S+): (\d+): (.*)$', l.strip())
    if m: base['TCSlib/Complexity/' + m.group(1)] = (int(m.group(2)), [x.strip() for x in m.group(3).split(',')])
root = sys.argv[3]
def parse(paths):
    mods, rcs, diags, cur = [], {}, [], None
    for p in paths:
        for l in open(p, encoding='utf-8', errors='replace'):
            m = re.match(r'^=== (\S+) start', l)
            if m: cur = m.group(1); mods.append(cur); continue
            m = re.match(r'^=== (\S+) end .* rc=(\d+)', l)
            if m: rcs[m.group(1)] = int(m.group(2)); continue
            m = re.match(r'^(TCSlib/\S+\.lean):(\d+):(\d+): (error|warning)(?:\([^)]*\))?: (.*)$', l.rstrip('\n'))
            if m: diags.append((m.group(1), int(m.group(2)), int(m.group(3)), m.group(4), m.group(5), cur))
    return mods, rcs, diags
_dcache = {}
def owner(f, ln):
    if f not in _dcache:
        p = os.path.join(root, f)
        _dcache[f] = decls(open(p, encoding='utf-8').read()) if os.path.exists(p) else []
    o = None
    for _, n, l, _ in _dcache[f]:
        if l <= ln: o = n
    return o
def report(label, paths, owned_file_lines=None):
    mods, rcs, diags = parse(paths)
    print(f'== {label}: {len(mods)} modules; order == order list: {mods == order}; rc != 0: {[m for m in mods if rcs.get(m) != 0]}')
    print(f'   errors: {sum(1 for d in diags if d[3] == "error")}; diagnostics attributed to another module: {sum(1 for d in diags if d[0][:-5] != d[5])}')
    sor = {}
    for f, ln, col, kind, msg, cur in diags:
        if kind == 'warning' and "declaration uses 'sorry'" in msg:
            sor.setdefault(f[:-5], []).append((ln, owner(f, ln) if 'WindowClock' not in f else f'line {ln}'))
    tot = sum(len(v) for v in sor.values())
    print(f'   sorry warnings: {tot} in {len(sor)} modules')
    for m in sorted(sor): print(f'     {m}: {len(sor[m])}: {[o for _, o in sor[m]]}')
    return mods, diags, sor
fin_mods, fin_diags, fin_sor = report('final sweep', [sys.argv[4]])
boot_mods, boot_diags, boot_sor = report('bootstrap (stage 1 + stage 2)', sys.argv[5:])
exp = {m: v for m, v in base.items() if not m.endswith('WindowClock')}
print('\nbase set:', sum(v[0] for v in base.values()), 'entries in', len(base), 'modules')
ok_boot = {m: len(v) for m, v in boot_sor.items()} == {m: v[0] for m, v in base.items()}
ok_fin = {m: len(v) for m, v in fin_sor.items()} == {m: v[0] for m, v in exp.items()}
print('bootstrap per-module counts == base set:', ok_boot)
print('final per-module counts == base set minus the target:', ok_fin)
nm = all(sorted(o for _, o in fin_sor.get(m, [])) == sorted(n.replace('_root_.Turing.', '').split('.')[-1] if False else n for n in v[1]) or True for m, v in exp.items())
mism = []
for m, (cnt, names) in exp.items():
    got = [o for _, o in fin_sor.get(m, [])]
    short = lambda n: n.split('.')[-1]
    if sorted(map(short, got)) != sorted(map(short, names)): mism.append((m, got, names))
print('final sorried declarations == base names (by short name):', not mism, mism[:3])
strip = lambda ds: sorted((f, ln, col, kind, msg) for f, ln, col, kind, msg, cur in ds if 'WindowClock' not in f)
print('diagnostics outside WindowClock identical bootstrap vs final:', strip(boot_diags) == strip(fin_diags),
      f'({len(strip(fin_diags))} diagnostics)')
print('WindowClock diagnostics, final sweep:', [(ln, kind, msg[:60]) for f, ln, col, kind, msg, cur in fin_diags if 'WindowClock' in f])
print('WindowClock diagnostics, bootstrap:', [(ln, kind, msg[:60]) for f, ln, col, kind, msg, cur in boot_diags if 'WindowClock' in f])
