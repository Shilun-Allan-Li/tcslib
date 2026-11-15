#!/usr/bin/env python3
"""Paired seal controls of the prf-long fill: scratch/controls/Controls.lean run unsealed and under the
four seal variants (requests: the final census of the owned file's import closure plus the helper
modules themselves, i.e. every TCSlib definition the controls can see; exemptions as in seals.py).
Errors are attributed to the `CONTROL`/`READER` comment above them.
usage: controls2.py OUTDIR"""
import json, os, re, subprocess, sys

R = '/workspace/plong'
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
src = open(f'{R}/scratch/controls/Controls.lean').read()
LP = f'{R}/.lake/tcslib-check-oleans:' + ':'.join(
    f'{R}/.lake/packages/{d}/.lake/build/lib/lean' for d in sorted(os.listdir(R + '/.lake/packages')))
ENV = dict(os.environ, LEAN_PATH=LP, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
sys.path.insert(0, '/workspace/pltools')
EVAL = 'Complexity.PolyExpr.eval'
COE = {'TCSlib.InformationTheory.FinDist.instCoeFunForallReal'}
# census of everything the controls import (written by the first run, unsealed)
census = f'{out}/census-controls.log'
if not os.path.exists(census) or 'TOTAL' not in open(census).read():
    CEN = open('/workspace/pltools/seals.py').read().split("CENSUS = '''", 1)[1].split("'''", 1)[0]
    CEN = CEN.replace('\\\\', '\\')
    p = f'{R}/scratch/controls/Census_controls.lean'
    open(p, 'w').write('import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF\n' + CEN % ('controls', 'Controls'))
    r = subprocess.run(['lean', p], cwd=R, env=ENV, capture_output=True, text=True)
    open(census, 'w').write(r.stdout + r.stderr)
cat = [l.rstrip('\n').split('\t') for l in open(census) if l.startswith('CAT\t')]
rows = sorted(c[1] for c in cat if c[3] == 'def' and (c[6] == 'true' or c[4] != 'reducible'))
HARN = open('/workspace/pltools/seals.py').read().split("HARNESS = '''", 1)[1].split("'''", 1)[0]
HARN = HARN.replace('\\\\', '\\')
def harness(rs, verify, label):
    s = ''
    for i in range(0, max(len(rs), 1), 400):
        s += HARN % (json.dumps('\n'.join(rs[i:i + 400])), 'true' if verify else 'false',
                     f'SEAL-{"VERIFY" if verify else "INSTALL"} {label} part {i // 400 + 1}:')
    return s
variants = {'unsealed': None, 'strict-A': (False, False), 'strict-B': (True, False),
            'coe-A': (False, True), 'coe-B': (True, True)}
results = []
for var, v in variants.items():
    if v is None:
        text = src.replace('-- SEAL-HERE', '-- (no seal)')
    else:
        rs = [r for r in rows if (v[0] or r != EVAL) and not (v[1] and r in COE)]
        text = 'import Lean\n' + src.replace('-- SEAL-HERE', harness(rs, False, var)) + harness(rs, True, var)
    path = f'{R}/scratch/controls/Controls_{var.replace("-", "")}.lean'
    open(path, 'w').write(text)
    p = subprocess.run(['lean', path], cwd=R, env=ENV, capture_output=True, text=True)
    log = p.stdout + p.stderr
    open(f'{out}/controls-{var}.log', 'w').write(log + f'\nEXIT {p.returncode}\n')
    lines = text.split('\n')
    marks = [(i + 1, l.strip('- ').strip()) for i, l in enumerate(lines)
             if l.startswith('-- CONTROL') or l.startswith('-- READER') or l.startswith('-- PROBE')]
    per = {m[1].split(' (')[0]: 0 for m in marks}
    for m in re.finditer(r'^\S+\.lean:(\d+):\d+: error[:(]', log, re.M):
        ln = int(m.group(1))
        lab = max([mk for mk in marks if mk[0] <= ln], default=(0, 'HARNESS'))[1].split(' (')[0]
        per[lab] = per.get(lab, 0) + 1
    rec = dict(variant=var, exit=p.returncode, errors_by_example=per,
               requests=0 if v is None else len(rs))
    results.append(rec)
    print(json.dumps(rec))
open(f'{out}/results.json', 'w').write(json.dumps(results, indent=1) + '\n')
