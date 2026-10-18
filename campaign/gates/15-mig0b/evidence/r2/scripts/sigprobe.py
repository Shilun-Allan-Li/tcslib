"""Signature-freeze probes (standard library only; python3 -I).

Usage:
  python3 -I sigprobe.py make <worktree> <outdir>      writes <outdir>/work/sig/*.lean
  python3 -I sigprobe.py compare <outdir>              compares the elaboration outputs

Each probe prints `#check @Name` under `set_option pp.all true` (fully explicit terms, universe
levels and instances). The *old* probes import the existing modules (the landed MIG-0a file, the
existing Build/Seam and Build/CounterLoop, Build/Catalog and Build/Embed) or copy the round-1
adapters file; the *new* probe is the fit file, whose closure holds every landing module. A
declaration's type is frozen when its two printed types are equal as text.
"""
import importlib.util
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('blocks', os.path.join(HERE, 'blocks.py'))
blocks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(blocks)
TM = 'TCSlib/Complexity/TuringMachine/'


def public(text, prefix_filter=None):
    lines, its = blocks.items(text)
    out = []
    for k, nm, s, e in its:
        if k != 'decl':
            continue
        blk = lines[s:e]
        decl = next(l for l in blk if blocks.DECL.match(l))
        if re.match(r'^(@\[[^\]]*\]\s*)?(\w+\s+)*private\b', decl) or decl.startswith('private'):
            continue
        out.append(nm)
    return out


def make(wt, out):
    read = lambda p: open(os.path.join(wt, p), encoding='utf-8').read()
    d = os.path.join(out, 'work', 'sig')
    os.makedirs(d, exist_ok=True)
    landed = public(read(TM + 'Build/Contract.lean'))
    seam_old = public(read(TM + 'Build/Seam.lean'))
    cl_old = public(read(TM + 'Build/CounterLoop.lean'))
    moved = ['Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc',
             'Turing.MultiTapeTM.runFrom_mapState_of_agreeOn']
    A = read('audits/evidence/mig0b/Contract-mig0b-adapters.lean.txt')
    Al = A.split('\n')
    D = read('audits/evidence/mig0b/Contract-mig0b-draft.lean.txt').split('\n')
    r1 = [n for t in ['\n'.join(D[1099:]), '\n'.join(Al[2663:])] for n in public(t)
          if '.MIG0bFit.' not in n]
    groups = {'mig0a': landed, 'seam': seam_old, 'counterloop': cl_old, 'moved': moved, 'r1': r1}
    json.dump(groups, open(os.path.join(d, 'groups.json'), 'w'), indent=1)

    def checks(names):
        return 'set_option pp.all true\n\n' + ''.join(f'#check @{n}\n' for n in names)

    hdr = lambda imps: ''.join(f'import {m}\n' for m in imps) + '\n'
    M = 'TCSlib.Complexity.TuringMachine.'
    files = {
        'old_mig0a.lean': hdr([M + 'Build.Contract']) + checks(landed),
        'old_seam.lean': hdr([M + 'Build.Seam']) + checks(seam_old),
        'old_counterloop.lean': hdr([M + 'Build.CounterLoop']) + checks(cl_old),
        'old_moved.lean': hdr([M + 'Build.Catalog', M + 'Build.Embed']) + checks(moved),
        'old_r1.lean': A.rstrip('\n') + '\n\n' + checks(r1),
    }
    fit = open([os.path.join(out, 'cut', f) for f in os.listdir(os.path.join(out, 'cut')) if f.startswith('TCSlib.Evidence.MIG0bR2Fit.')][0],
               encoding='utf-8').read()
    allnames = list(dict.fromkeys(landed + seam_old + cl_old + moved + r1))
    renamed = {'Turing.seamComp_right': 'Turing.seamCompTM_runFrom_right'}
    gone = {'Turing.counterLoopOrbit_eq_roundOrbit', 'Turing.Contract.mem_hull_left',
            'Turing.Contract.mem_hull_right', 'Turing.Contract.runFrom_state_none_mono'}
    files['new_all.lean'] = fit.rstrip('\n') + '\n\n' + checks(
        [renamed.get(n, n) for n in allnames if n not in gone])
    for f, t in files.items():
        open(os.path.join(d, f), 'w', encoding='utf-8').write(t)
    print('probes', len(files), {k: len(v) for k, v in groups.items()})


def parse_out(path):
    txt = open(path, encoding='utf-8').read()
    res, cur = {}, None
    for line in txt.split('\n'):
        m = re.match(r'^@?([A-Za-z_][^\s{]*?)(?:\.\{|\s)', line)
        if m:
            cur = m.group(1)
            res[cur] = [line]
        elif cur and (line.startswith(' ') or line == ''):
            res[cur].append(line)
        else:
            cur = None
    return {k: '\n'.join(v).rstrip() for k, v in res.items()}


def compare(out):
    d = os.path.join(out, 'work', 'sig')
    groups = json.load(open(os.path.join(d, 'groups.json')))
    new = parse_out(os.path.join(out, 'work', 'sigout', 'new_all.lean.out'))
    expected_diff = {'Turing.seamCompTM_runFrom_right', 'Turing.seamReleaseTM_runFrom_pos',
                     'Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc',
                     'Turing.embedEmitCfg_unselected', 'Turing.Cfg.select',
                     'Turing.embedEmitCfg_select', 'Turing.embedEmitCfg_eq',
                     'Turing.embedEmitCfg_mapState_eq', 'Turing.embedEmitCfg_ofWords_eq'}
    gone = {'Turing.counterLoopOrbit_eq_roundOrbit'}
    lines = []
    for g, f in [('mig0a', 'old_mig0a'), ('seam', 'old_seam'), ('counterloop', 'old_counterloop'),
                 ('moved', 'old_moved'), ('r1', 'old_r1')]:
        old = parse_out(os.path.join(out, 'work', 'sigout', f + '.lean.out'))
        same, diff, missing, upto = 0, [], [], []
        gen = '|'.join(re.escape(c) for c in sorted(expected_diff))
        for n in groups[g]:
            if n in gone:
                continue
            assert n in old, (g, n)
            if n not in new:
                missing.append(n)
            elif old[n] == new[n]:
                same += 1
            elif re.sub(r'(@(?:' + gen + r'))\.\{0, 0\}', r'\1', new[n]) == old[n]:
                upto.append(n)
            else:
                diff.append(n)
        unexpected = [n for n in diff if n not in expected_diff]
        lines.append(f'* {g}: {len(groups[g])} public declarations; {same} printed types '
                     f'identical; identical up to the universe instantiation `.{{0, 0}}` of a '
                     f'generalized constant they mention: {upto or "none"}; differing (the '
                     f'generalizations themselves): {diff or "none"}; missing in the new '
                     f'closure: {missing or "none"}')
        assert not unexpected and not missing, (g, unexpected, missing)
    print('\n'.join(lines))
    open(os.path.join(out, 'work', 'signatures.log'), 'w', encoding='utf-8').write(
        '\n'.join(lines) + '\n')


if __name__ == '__main__':
    if sys.argv[1] == 'make':
        make(sys.argv[2], sys.argv[3])
    else:
        compare(sys.argv[2])
