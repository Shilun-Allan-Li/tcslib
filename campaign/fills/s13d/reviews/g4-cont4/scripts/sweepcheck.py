import sys, re
def parse(p):
    mods = []; sorries = []; timing = {}; cur = None; diag_by_mod = {}
    for l in open(p, encoding='utf-8', errors='replace'):
        m = re.match(r'^== MODULE (\S+)', l)
        if m: cur = m.group(1); mods.append(cur); diag_by_mod[cur] = []; continue
        m = re.match(r'^== TIMING (\S+): start (\S+) end (\S+) elapsed ([\d.]+)s maxrss (\d+) MiB exit (\d+)', l)
        if m: timing[m.group(1)] = (float(m.group(4)), int(m.group(5)), int(m.group(6)), m.group(2), m.group(3)); continue
        m = re.match(r"^(\S+\.lean):(\d+):(\d+): (warning|error): (.*)", l)
        if m and cur:
            diag_by_mod[cur].append((m.group(1), m.group(2), m.group(4), m.group(5).strip()))
            if "declaration uses 'sorry'" in l: sorries.append((cur, m.group(1), m.group(2)))
    return mods, sorries, timing, diag_by_mod
order = [l.strip() for l in open(sys.argv[1]) if l.strip()]
for p in sys.argv[2:]:
    mods, sorries, timing, diags = parse(p)
    print('==', p.split('/')[-1])
    print(' modules', len(mods), 'order list equal and in order:', mods == order)
    print(' all exit 0:', all(t[2] == 0 for t in timing.values()), '; timed', len(timing))
    print(' error lines:', sum(1 for m in diags for d in diags[m] if d[2] == 'error'))
    print(' sorry warnings:', len(sorries))
    bym = {}
    for m, f, ln in sorries: bym.setdefault(m, []).append(ln)
    for m in bym: print('   ', m, bym[m])
    mx = max(timing.items(), key=lambda kv: kv[1][1]); lg = max(timing.items(), key=lambda kv: kv[1][0])
    print(' peak maxrss', mx[1][1], 'MiB at', mx[0], '; longest', lg[1][0], 's at', lg[0])
    zr = 'TCSlib/Complexity/TuringMachine/Build/ZoneRebalance'
    print(' ZoneRebalance timing', timing.get(zr), 'diagnostics', len(diags.get(zr, [])), diags.get(zr, [])[:5])
    print(' first start', min(t[3] for t in timing.values()), 'last end', max(t[4] for t in timing.values()))

if len(sys.argv) == 4:
    a = parse(sys.argv[2])[3]; b = parse(sys.argv[3])[3]
    zr = 'TCSlib/Complexity/TuringMachine/Build/ZoneRebalance'
    diff = [m for m in a if m != zr and a[m] != b.get(m)]
    print('modules (other than ZoneRebalance) whose diagnostics differ bootstrap vs final:', diff)
    print('total diagnostics outside ZoneRebalance:', sum(len(a[m]) for m in a if m != zr), sum(len(b[m]) for m in b if m != zr))
