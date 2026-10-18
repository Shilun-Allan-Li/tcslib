"""Axiom probe (standard library only; python3 -I).

Usage:
  python3 -I axprobe.py make <outdir>      writes <outdir>/work/ax/AxProbe.lean: a copy of the fit
                                           file (closure: every landing module) with `#print axioms`
                                           for every public declaration of the unit's parts and of
                                           the fit namespace
  python3 -I axprobe.py summary <outdir>   classifies the printed axioms
"""
import importlib.util
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('sigprobe', os.path.join(HERE, 'sigprobe.py'))
sp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sp)
STD = {'propext', 'Classical.choice', 'Quot.sound'}


def make(out):
    unit = open(os.path.join(out, 'Contract-mig0b-r2-unit.lean'), encoding='utf-8').read()
    names = []
    for chunk in unit.split('\n/-! ' + '═' * 96)[1:]:
        body = chunk[chunk.index('\n', chunk.rindex('\n-- @')) + 1:]
        land = re.search(r'-- @landing (\S+)', chunk).group(1)
        for n in sp.public(body):
            names.append((land, n))
    fit = open(os.path.join(out, 'fit-tests.lean'), encoding='utf-8').read()
    names += [('fit', n) for n in sp.public(fit)]
    src = open([os.path.join(out, 'cut', f) for f in os.listdir(os.path.join(out, 'cut')) if f.startswith('TCSlib.Evidence.MIG0bR2Fit.')][0],
               encoding='utf-8').read()
    d = os.path.join(out, 'work', 'ax')
    os.makedirs(d, exist_ok=True)
    open(os.path.join(d, 'AxProbe.lean'), 'w', encoding='utf-8').write(
        src.rstrip('\n') + '\n\n' + ''.join(f'#print axioms {n}\n' for _, n in names))
    json.dump(names, open(os.path.join(d, 'names.json'), 'w'), indent=0)
    print('prints', len(names))


def summary(out):
    names = json.load(open(os.path.join(out, 'work', 'ax', 'names.json')))
    txt = open(os.path.join(out, 'work', 'ax', 'AxProbe.lean.out'), encoding='utf-8').read()
    txt = re.sub(r'\n\s+', ' ', txt)
    res = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", txt):
        res[m.group(1)] = {a.strip() for a in m.group(2).split(',')}
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", txt):
        res[m.group(1)] = set()
    lines, sorry, nonstd = [], [], []
    by_land = {}
    for land, n in names:
        assert n in res, n
        by_land.setdefault(land, []).append(n)
        if 'sorryAx' in res[n]:
            sorry.append(n)
        if res[n] - STD - {'sorryAx'}:
            nonstd.append(n)
    lines.append(f'printed: {len(names)} (every public declaration of the 13 parts, and of the '
                 f'fit namespace); outputs parsed: {len(res)}')
    for land, ns in by_land.items():
        lines.append(f'* {land}: {len(ns)}')
    lines.append(f'depending on sorryAx: {sorry}')
    lines.append(f'depending on an axiom outside propext, Classical.choice, Quot.sound: '
                 f'{nonstd or "none"}')
    print('\n'.join(lines))
    open(os.path.join(out, 'work', 'axioms-summary.log'), 'w', encoding='utf-8').write(
        '\n'.join(lines) + '\n')


if __name__ == '__main__':
    (make if sys.argv[1] == 'make' else summary)(sys.argv[2])
