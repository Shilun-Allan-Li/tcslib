import sys, re, os
# usage: sweep.py <worktree for names> <order list> <base sorries> <bootstrap log> <sweep log> <owned-final log>
wt, order, basef, boot, sw, own = sys.argv[1:7]
mods = [l.strip() for l in open(order) if l.strip() and not l.startswith('#')]
H = re.compile(r'^=== (TCSlib\S*) (start |final-check )?(\d\d:\d\d:\d\d)')
W = re.compile(r'^(TCSlib/\S+)\.lean:(\d+):(\d+): warning: declaration uses .sorry.')
E = re.compile(r'^(TCSlib/\S+)\.lean:(\d+):(\d+): error')
def parse(p):
    runs = {}; order_seen = []; cur = None; fails = []
    for l in open(p, encoding='utf-8', errors='replace'):
        m = H.match(l)
        if m and not l.rstrip().endswith(' end ' + m.group(3)) and ' end ' not in l:
            cur = m.group(1); order_seen.append((cur, m.group(3))); runs.setdefault(cur, []).append({'sorry': [], 'err': []}); continue
        if l.startswith('FAIL('): fails.append(l.strip())
        m = W.match(l)
        if m and cur: runs[m.group(1)] = runs.get(m.group(1)) or [{'sorry': [], 'err': []}]; runs[m.group(1)][-1]['sorry'].append(int(m.group(2)))
        m = E.match(l)
        if m and cur: runs[m.group(1)][-1]['err'].append(l.strip())
    return runs, order_seen, fails
def name_at(mod, line):
    src = open(os.path.join(wt, mod + '.lean'), encoding='utf-8').read().split('\n')
    m = re.match(r'.*?(theorem|lemma|def|abbrev|instance)\s+(\S+)', src[line - 1])
    return m.group(2) if m else f'?{line}'
b, bo, bf = parse(boot); s, so, sf = parse(sw); o, oo, of = parse(own)
print(f'bootstrap: {len(bo)} module runs, {len(b)} modules, fails {bf}')
print(f'sweep: {len(so)} module runs, {len(s)} modules, fails {sf}')
dup = sorted({m for m, _ in so if sum(1 for n, _ in so if n == m) > 1})
print('sweep modules run more than once:', dup)
print(f'owned-final: {len(oo)} run(s) {oo}')
covered = set(b) | set(s)
print('order-list modules in neither log:', [m for m in mods if m not in covered])
print('modules in both logs:', sorted(set(b) & set(s)))
print('log modules outside the order list:', sorted(covered - set(mods)))
# final state per module: owned-final > sweep (last run) > bootstrap (last run)
final = {}
for src in (b, s, o):
    for m, rs in src.items(): final[m] = rs[-1]
errs = {m: r['err'] for m, r in final.items() if r['err']}
print('errors in the last run of any module:', errs)
base = {}
for l in open(basef):
    m = re.match(r'(\S+): (\d+): (.*)', l.strip())
    if m: base['TCSlib/Complexity/' + m.group(1)] = sorted(x.strip().replace(' [private]', '').split('.')[-1] for x in m.group(3).split(','))
tot = 0; diffs = []
for m in mods:
    got = sorted(name_at(m, ln) for ln in final.get(m, {'sorry': []})['sorry'])
    tot += len(got)
    exp = base.get(m, [])
    if [g.split('.')[-1] for g in got] != exp: diffs.append((m, exp, got))
print(f'final sorry warnings: {tot} in {sum(1 for m in mods if final.get(m, {"sorry": []})["sorry"])} modules')
for d in diffs: print('DIFF', d[0], 'base', d[1], 'final', d[2])
