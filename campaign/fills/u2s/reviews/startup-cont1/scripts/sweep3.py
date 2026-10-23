"""Worker sweep log (START i/N M t / END i/N M t EXIT e WALL_SECONDS w MAX_RSS_KIB r) vs the order
list and the base sorry set; sorry warnings mapped to declaration names via the given tree.
usage: python3 -I sweep3.py <log> <order list> <base sorries> <tree root> <label>"""
import re, sys, os
log = open(sys.argv[1], encoding='utf-8', errors='replace').read().split('\n')
order = [l.strip() for l in open(sys.argv[2], encoding='utf-8') if l.strip() and not l.startswith('#')]
root = sys.argv[4]
mods, exits, times, wall, rss = [], {}, {}, 0.0, 0
for l in log:
    m = re.match(r'^START (\d+)/(\d+) (\S+) (\S+)', l)
    if m: mods.append(m.group(3)); times[m.group(3)] = [m.group(4), None]; continue
    m = re.match(r'^END (\d+)/(\d+) (\S+) (\S+) EXIT (\d+) WALL_SECONDS (\S+) MAX_RSS_KIB (\d+)', l)
    if m:
        exits[m.group(3)] = int(m.group(5)); times[m.group(3)][1] = m.group(4)
        wall += float(m.group(6)); rss = max(rss, int(m.group(7)))
print(sys.argv[5])
print('module records:', len(mods), '; with an END/exit record:', len(exits), '; order list:', len(order))
print('sequence == order list:', mods == order)
print('nonzero exits:', {m: e for m, e in exits.items() if e} or 'none')
print('error lines:', [l for l in log if re.search(r':\d+:\d+: error', l)][:5] or 'none')
print('summed wall %.3f s; max RSS %d KiB' % (wall, rss))
per = {}
for l in log:
    m = re.match(r"^(TCSlib/\S+)\.lean:(\d+):\d+: warning: declaration uses 'sorry'", l)
    if m:
        f = m.group(1) + '.lean'; n = int(m.group(2))
        src = open(os.path.join(root, f), encoding='utf-8').read().split('\n')[n - 1]
        mm = re.search(r'(?:theorem|lemma|def|abbrev|instance)\s+(\S+)', src)
        name = mm.group(1) if mm else '?'
        if src.lstrip().startswith('private'): name += ' [private]'
        per.setdefault(m.group(1).replace('TCSlib/Complexity/', ''), []).append(name)
print('sorry warnings: %d in %d modules' % (sum(len(v) for v in per.values()), len(per)))
base = {}
for l in open(sys.argv[3], encoding='utf-8'):
    m = re.match(r'^(\S+): (\d+): (.*)$', l.strip())
    if m: base[m.group(1)] = sorted(x.strip() for x in m.group(3).split(','))
print('base set: %d in %d modules' % (sum(len(v) for v in base.values()), len(base)))
def norm(x): return x.replace('_root_.Turing.FinTM.', '').replace('_root_.', '')
for k in sorted(set(per) | set(base)):
    a = sorted(norm(x) for x in per.get(k, [])); b = sorted(norm(x) for x in base.get(k, []))
    flag = '' if a == b else '<-- differs: sweep %s base %s' % (a, b)
    print('   %-42s sweep %d  base %d %s' % (k, len(a), len(b), flag))
u = 'TCSlib/Complexity/TuringMachine/UniversalK'
print('owned module START/END:', times.get(u), '; first/last record:', times.get(mods[0]) if mods else None, times.get(mods[-1]) if mods else None)
