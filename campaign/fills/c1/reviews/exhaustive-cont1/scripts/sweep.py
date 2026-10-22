"""Worker sweep log vs the order list and the base sorry set.
usage: python3 -I sweep.py <log> <order list> <base sorries> [<module subset label>]"""
import re, sys
log = open(sys.argv[1], encoding='utf-8', errors='replace').read().split('\n')
order = [l.strip() for l in open(sys.argv[2], encoding='utf-8') if l.strip() and not l.startswith('#')]
mods, exits, rss = [], {}, {}
for l in log:
    m = re.match(r'^### (\S+): start (\S+) end (\S+) wall (\S+) maxrss (\d+) MiB exit (\d+)', l)
    if m: mods.append(m.group(1)); exits[m.group(1)] = int(m.group(6)); rss[m.group(1)] = int(m.group(5))
print('module records:', len(mods), '; order list:', len(order))
print('sequence == order list:', mods == order)
if mods != order:
    sub = [m for m in order if m in set(mods)]
    print('   sequence == order list restricted to the logged modules:', mods == sub, '; logged not in list:', [m for m in mods if m not in order])
print('nonzero exits:', {m: e for m, e in exits.items() if e} or 'none')
print('error lines:', [l for l in log if re.search(r':\d+:\d+: error', l)][:5] or 'none')
print('max RSS (MiB):', max(rss.values()) if rss else None, max(rss, key=rss.get) if rss else None)
# sorry warnings by module, with the declaration line
per = {}
for l in log:
    m = re.match(r"^(TCSlib/\S+)\.lean:(\d+):\d+: warning: declaration uses 'sorry'", l)
    if m: per.setdefault(m.group(1).replace('TCSlib/Complexity/', ''), set()).add(int(m.group(2)))
print('sorry warnings: %d in %d modules' % (sum(len(v) for v in per.values()), len(per)))
base = {}
for l in open(sys.argv[3], encoding='utf-8'):
    m = re.match(r'^(\S+): (\d+): (.*)$', l.strip())
    if m: base[m.group(1)] = int(m.group(2))
for k in sorted(set(per) | set(base)):
    print('   %-40s sweep %s  base %s %s' % (k, len(per.get(k, ())), base.get(k, 0), '' if len(per.get(k, ())) == base.get(k, 0) else '<-- differs'))
