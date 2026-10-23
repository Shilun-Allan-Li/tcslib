import sys, re, collections, os
# usage: sweep.py <order list> <base sorries> <tree root for line->name> <log>...: per log, the modules
# checked in order, exit codes, every diagnostic, the sorry warnings by module and by declaration name.
order_f, base_f, root, logs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
order = [l.strip() for l in open(order_f) if l.strip()]
base = {}
for l in open(base_f, encoding='utf-8'):
    m = re.match(r'^(\S+): (\d+): (.*)$', l.strip())
    if m: base[m.group(1)] = sorted(x.strip() for x in m.group(3).split(','))
DECL = re.compile(r'^\s*(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)')
def name_at(path, line):
    L = open(os.path.join(root, path), encoding='utf-8').read().split('\n')
    m = DECL.match(L[line - 1])
    return m.group(5) if m else f'?{line}'
for lg in logs:
    txt = open(lg, encoding='utf-8', errors='replace').read().split('\n')
    checks = [re.match(r'^(?:CHECK|BUILD) (\S+)/(\d+) (\S+)', l) for l in txt]
    mods = [m.group(3) for m in checks if m and m.group(1) != 'owned']
    owned = [l for l in txt if l.startswith('CHECK owned')]
    exits = [l for l in txt if l.startswith('EXIT ')]
    nonzero = [l for l in exits if not l.startswith('EXIT 0')]
    diag = [l for l in txt if re.match(r'^\S+\.lean:\d+:\d+: (error|warning)', l)]
    errs = [l for l in diag if ': error' in l]
    sor = collections.defaultdict(list)
    for l in diag:
        m = re.match(r'^(TCSlib/Complexity/(\S+))\.lean:(\d+):\d+: warning: declaration uses .sorry.', l)
        if m: sor[m.group(2)].append(name_at(m.group(1) + '.lean', int(m.group(3))))
    print(f'== {os.path.basename(lg)}: CHECK/BUILD lines {len(mods)} (+{len(owned)} owned), distinct {len(set(mods))}, EXIT lines {len(exits)}, nonzero {len(nonzero)}; diagnostics {len(diag)}, errors {len(errs)}')
    for l in errs: print('   ERROR', l[:170])
    for l in nonzero[:5]: print('   NONZERO', l)
    print(f'   sorry warnings {sum(len(v) for v in sor.values())} in {len(sor)} modules')
    if len(set(mods)) == len(order):
        first = []; seen = set()
        for m in mods:
            if m not in seen: seen.add(m); first.append(m)
        print('   order (first occurrence) == order list:', first == order)
    cmp = {k: (sorted(base.get(k, [])), sorted(sor.get(k, []))) for k in set(base) | set(sor)}
    bad = {k: v for k, v in cmp.items() if v[0] != v[1]}
    print('   sorry names vs base set (all modules of the log):', 'identical' if not bad else bad)
    cf = [l for l in diag if 'Build/CfgRecord.lean' in l]
    print('   CfgRecord diagnostics:', len(cf), cf[:3])
