#!/usr/bin/env python3
"""Development seal check of one module's WORKING-TREE source (cleanup-part2 J work loop).

python3 -I sealwt.py <phase> <closure.tsv> <module path without .lean> [more modules...]

For each module: build the whole-file sealed probe from the working-tree file with
tools/mkseal.py (standing-rule notation left unsealed as in the standard variant), check it
with tools/chk.py (CHK_PHASE=seal-<phase>), and print every error mapped back to the source line
with its message head. Exit status 1 if any module has an error. Development evidence only; the
recorded seal runs use tools/sealrun.py on committed revisions."""
import sys, os, re, subprocess
phase, clog = sys.argv[1], sys.argv[2]
mods = sys.argv[3:]
CLONE = '/workspace/cp2/src'; EV = '/workspace/cp2/evidence/logs'
NOTATION = 'Complexity.PolyExpr.eval,Complexity.PolyExpr.eval.match_1,Complexity.PolyExpr.eval._sunfold'
bad = 0
for path in mods:
    mod = path.replace('/', '.')
    rel = f'.lake/cleanup-part2-probes/seal/{phase}/{path}'
    os.makedirs(os.path.dirname(f'{CLONE}/{rel}'), exist_ok=True)
    env = dict(os.environ, CP2_SEAL_NOTATION=NOTATION)
    subprocess.run(['python3', '-I', '/workspace/cp2/tools/mkseal.py', clog, mod, f'{CLONE}/{path}.lean',
                    f'{CLONE}/{rel}.lean'], check=True, capture_output=True, env=env)
    env2 = dict(os.environ, CHK_PHASE=f'seal-{phase}')
    r = subprocess.run(['python3', '-I', '/workspace/cp2/tools/chk.py', rel], env=env2, capture_output=True, text=True)
    print(r.stdout.strip(), flush=True)
    log = open(f'{EV}/seal-{phase}/modules/{rel}.log').read()
    probe = open(f'{CLONE}/{rel}.lean').read().split('\n')
    w = next(i for i, l in enumerate(probe) if l.startswith('-- CP2 WHOLE-FILE SEAL')) + 1
    b = next(i for i, l in enumerate(probe) if l == '-- CP2 END SEAL') + 1
    off = b - w + 2
    src = open(f'{CLONE}/{path}.lean').read().split('\n')
    parts = re.split(r'(?m)^(?=\S*\.lean:\d+:\d+: )', log)
    n = 0
    for p in parts:
        m = re.match(r'\S*\.lean:(\d+):(\d+): error[^:]*: ?', p)
        if not m: continue
        ln = int(m.group(1)); s = ln - off if ln > b else ln
        body = p[m.end():].split('CP2-EOF')[0].rstrip().split('\n')
        print(f'  ERR {path}:{s}:{m.group(2)}: {" | ".join(x.strip() for x in body[:6])[:400]}')
        n += 1
    if 'CP2-EOF' not in log: print('  HARNESS: no EOF marker'); n += 1
    bad += n
    print(f'  -- {n} errors in {path}')
sys.exit(1 if bad else 0)
