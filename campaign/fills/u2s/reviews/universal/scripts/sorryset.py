"""Sorry warnings and errors in a directory of per-module logs, mapped to declaration names in a
source tree. Usage: sorryset.py <tree root> <log dir> [<log dir2> ...]"""
import os, re, sys
root = sys.argv[1]
D = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance|structure)\s+(\S+)')
def name_at(path, line):
    L = open(os.path.join(root, path), encoding='utf-8').read().split('\n')
    m = D.match(L[line - 1])
    return m.group(1) if m else f'?{line}'
res = {}; errs = []; exits = {}; mods = {}
for d in sys.argv[2:]:
    for f in sorted(os.listdir(d)):
        if not f.endswith('.log'): continue
        t = open(os.path.join(d, f), encoding='utf-8', errors='replace').read()
        mod = f.split('-', 1)[1][:-4].replace('__', '/')
        mods[mod] = d
        for m in re.finditer(r'^(\S+\.lean):(\d+):\d+: warning: declaration uses .sorry.', t, re.M):
            res.setdefault((m.group(1), int(m.group(2))), mod)
        for m in re.finditer(r'^(\S+\.lean):(\d+):\d+: error', t, re.M): errs.append((mod, m.group(0)))
        e = re.findall(r'EXIT (\d+)', t); exits[mod] = e[-1] if e else '?'
names = sorted(f'{p[len("TCSlib/Complexity/"):-5]}: {name_at(p, l)}' for (p, l) in res)
print('modules', len(mods), '; nonzero exits', [m for m, e in exits.items() if e != '0'], '; errors', errs)
print('sorry warnings', len(names))
for n in names: print('  ', n)
