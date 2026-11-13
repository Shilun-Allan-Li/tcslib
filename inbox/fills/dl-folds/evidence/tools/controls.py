#!/usr/bin/env python3
"""Paired seal controls (dl-folds): writes the unsealed, sealed and sealed-with-`PolyExpr.eval`-open
variants of scratch/controls/SealControls.lean (the line `-- SEAL-HERE` becomes the seal), runs
each with the olean tree, and records exit status and the error lines.
usage: controls.py OUTDIR"""
import os, re, subprocess, sys
F = '/workspace/folds'
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
src = open(f'{F}/scratch/controls/SealControls.lean').read()
TARGETS = ['TCSlib.Cryptography.Games.iterEmit', 'TCSlib.Cryptography.Games.InteractiveHandler.rAns',
           'TCSlib.Cryptography.Games.InteractiveHandler.finA', 'TCSlib.Cryptography.Games.ansRead',
           'TCSlib.Cryptography.Games.cntRead', 'TCSlib.Cryptography.coinBlock',
           'TCSlib.Cryptography.Composability.NMCCA2.logEmit',
           'TCSlib.Cryptography.Composability.NMSim.chunkMap',
           'TCSlib.Cryptography.Games.fwdHandler']
EVAL = 'Complexity.PolyExpr.eval'
variants = {
    'unsealed': '-- (no seal)',
    'sealed': 'attribute [local irreducible] ' + ' '.join('_root_.' + t for t in [EVAL] + TARGETS),
    'sealed-evalopen': 'attribute [local irreducible] ' + ' '.join('_root_.' + t for t in TARGETS),
}
LP = F + '/.lake/tcslib-check-oleans:' + ':'.join(
    f'{F}/.lake/packages/{d}/.lake/build/lib/lean' for d in sorted(os.listdir(F + '/.lake/packages')))
env = dict(os.environ, LEAN_PATH=LP, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
ex_lines = [i + 1 for i, l in enumerate(src.splitlines()) if l.startswith('example')]
for name, seal in variants.items():
    text = src.replace('-- SEAL-HERE', seal)
    path = f'{F}/scratch/controls/SealControls_{name.replace("-", "_")}.lean'
    open(path, 'w').write(text)
    p = subprocess.run(['lean', path], cwd=F, env=env, capture_output=True, text=True)
    log = p.stdout + p.stderr
    open(f'{out}/seal-controls-{name}.log', 'w').write(log)
    errs = [int(m.group(1)) for m in re.finditer(r'\.lean:(\d+):\d+: error', log)]
    per = {}
    for e in errs:
        ex = max([x for x in ex_lines if x <= e], default=None)
        per[ex] = per.get(ex, 0) + 1
    print(f'{name}: exit {p.returncode}, {len(errs)} errors; examples failing: '
          f'{sorted(per)} (per example: {sorted(per.values())}); examples at {ex_lines}')
