"""Compare the sweep's `sorry` warnings with base-sorries.txt (python3 -I).

usage: sorries.py ROOT SWEEP_LOG_DIR BASE_SORRIES ORDER [--expect-removed NAME,...]
Reads each module's sweep log (named like the bootstrap logs: path with `/` -> `_`), maps every
`declaration uses 'sorry'` warning to the declaration at that line of the module's source in
ROOT, and compares the per-module sets with base-sorries.txt. Prints the removed and added
declarations; PASS when nothing is added and the removed set equals the expected one.
"""
import re, sys
from pathlib import Path

root, logdir, base, order = sys.argv[1:5]
expect = set()
if '--expect-removed' in sys.argv:
    expect = set(sys.argv[sys.argv.index('--expect-removed') + 1].split(','))
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance)\s+(\S+)')
basemap = {}
for l in open(base):
    m = re.match(r'(\S+): \d+: (.*)$', l.strip())
    if m:
        basemap[m[1]] = {x.strip() for x in m[2].split(',')}
now = {}
for mod in open(order).read().split():
    log = Path(logdir) / (mod.replace('/', '_') + '.log')
    src = (Path(root) / (mod + '.lean')).read_text().splitlines()
    names = set()
    for m in re.finditer(r"^\S+\.lean:(\d+):\d+: warning: declaration uses 'sorry'", log.read_text(),
                         re.M):
        ln = int(m[1])
        name = next((DECL.match(src[i])[1] for i in range(ln - 1, -1, -1) if DECL.match(src[i])),
                    '?')
        names.add(name)
    if names:
        now[mod] = names
removed, added = [], []
for mod in sorted(set(basemap) | set(now)):
    b, n = basemap.get(mod, set()), now.get(mod, set())
    removed += [f'{mod}: {x}' for x in sorted(b - n)]
    added += [f'{mod}: {x}' for x in sorted(n - b)]
    print(f'{mod}: base {len(b)} now {len(n)}: {", ".join(sorted(n)) or "-"}')
print(f'TOTAL base {sum(map(len, basemap.values()))} now {sum(map(len, now.values()))}')
print(f'removed ({len(removed)}):')
for x in removed:
    print('  - ' + x)
print(f'added ({len(added)}):' + ''.join('\n  + ' + x for x in added))
got = {x.split(': ', 1)[1] for x in removed}
ok = not added and (not expect or got == expect)
print('ADMISSIONS ' + ('PASS' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
