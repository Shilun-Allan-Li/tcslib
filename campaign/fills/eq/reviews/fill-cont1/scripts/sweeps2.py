"""Summarize a delivered sweep log of the form '=== [i] <module>' ... 'TIMING <module> start= end=
wall= maxrss_kib= exit=' (python3 -I; data only).  For the sorry warnings, the declaration at the
warned line is read from the source at <rev> (git show).
usage: python3 -I sweeps2.py <log> <order list> <git dir> <rev>"""
import re, subprocess, sys
from collections import OrderedDict
logp, order_p, gd, rev = sys.argv[1:5]
order = [l.strip() for l in open(order_p) if l.strip() and not l.startswith('#')]
T = open(logp, encoding='utf-8').read().split('\n')
W = re.compile(r"^(\S+\.lean):(\d+):(\d+): (warning|error): (.*)$")
TM = re.compile(r'^TIMING (\S+) start=(\S+) end=(\S+) wall=([\d.]+)s maxrss_kib=(\d+) exit=(\d+)')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma|def|abbrev|instance|structure)\s+(\S+)')
cache = {}
def decl_at(path, line):
    if path not in cache:
        cache[path] = subprocess.run(['git', '-C', gd, 'show', f'{rev}:{path}'], capture_output=True, text=True).stdout.split('\n')
    L = cache[path]; m = DECL.match(L[line - 1]) if line - 1 < len(L) else None
    return m.group(1) if m else '?'
mods = OrderedDict(); cur = None
for l in T:
    m = re.match(r'^=== \[(\d+)\] (\S+)', l)
    if m: cur = m.group(2); mods[cur] = {'w': [], 'e': 0, 's': [], 't': None}; continue
    m = TM.match(l)
    if m: mods[m.group(1)]['t'] = m.groups(); continue
    m = W.match(l)
    if m and cur:
        if m.group(4) == 'error': mods[cur]['e'] += 1
        elif "declaration uses 'sorry'" in m.group(5): mods[cur]['s'].append(decl_at(m.group(1), int(m.group(2))))
        else: mods[cur]['w'].append(l[:150])
names = list(mods)
print(f'modules {len(names)}; equal to the order list in order: {names == order}')
print('first/last lines:', T[0][:150], '|', [x for x in T if x.startswith('SWEEP OK') or x.startswith('exit=')])
print('exits nonzero:', [k for k, v in mods.items() if v['t'] and v['t'][5] != '0'], '; missing TIMING:', [k for k, v in mods.items() if not v['t']])
print('errors:', sum(v['e'] for v in mods.values()))
tot = sum(float(v['t'][3]) for v in mods.values() if v['t']); pk = max(mods.items(), key=lambda kv: int(kv[1]['t'][4]) if kv[1]['t'] else 0)
print(f'summed wall {tot:.1f}s; peak maxrss {pk[1]["t"][4]} KiB ({pk[0]})')
S = {k: v['s'] for k, v in mods.items() if v['s']}
print(f'sorry warnings: {sum(len(v) for v in S.values())} in {len(S)} modules')
for k, v in S.items(): print(f'   {k}: {len(v)}: {", ".join(v)}')
print('other warnings per module (count):', {k: len(v['w']) for k, v in mods.items() if v['w']})
o = 'TCSlib/Complexity/Diagonalization/NTimeDiagonalizer'
print('NTimeDiagonalizer:', mods.get(o, {}).get('t'), 'other warnings:', mods.get(o, {}).get('w'))
