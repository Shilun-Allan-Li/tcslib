"""Sealed copies and seal controls for the ARM embedding API PR (rule 10).

Usage: python3 -I mkseal_arm.py <worktree> <outdir>
Each sealed copy is the head file with its new declarations moved to the end of the file, inside a
section that makes every other-file TCSlib definition they could reach locally irreducible and
erases the four @[simp] TCSlib definitions. Controls: one delta control per sealed definition, an
equation control for the recursive ones, unsealed and sealed.
"""
import sys, pathlib
wt, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
P = 'TCSlib/Complexity/SpaceComplexity/'
NS = 'Complexity.LogProg.'
ERASE = 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg'

def seal(names):
    return ERASE + '\nattribute [local irreducible]\n' + '\n'.join('  ' + NS + n for n in names) + '\n'

def cut(text, start, end):
    i = text.index(start); j = text.index(end, i)
    assert text.count(start) == 1
    return text[:i] + text[j:], text[i:j]

def tail_append(text, block, closers):
    assert text.endswith(closers), closers
    return text[:-len(closers)] + block + closers

jobs = []
# ARM: the step equations
t = (wt / (P + 'Machines/ARM.lean')).read_text()
t, blk = cut(t, '/-! ## One step, instruction by instruction', '/-! ## Compilation -/')
blk = blk.replace('section Steps\n', 'section Steps\n\n' + seal(['callSegs', 'vword', 'argSegs', 'Mode.seg0', 'ValidPlain', 'ValidPair']), 1)
jobs.append(('ARMSealed', tail_append(t, '\n' + blk, '\nend Complexity.LogProg\n')))
# ARMProof: the embedding section (already last)
t = (wt / (P + 'Machines/ARMProof.lean')).read_text()
assert t.count('section Embed\n') == 1
t = t.replace('section Embed\n', 'section Embed\n\n' + seal(['astep', 'arun', 'callSegs', 'vword', 'argSegs', 'Mode.seg0', 'ValidPlain', 'ValidPair', 'plainWord', 'pairWords']), 1)
jobs.append(('ARMProofSealed', t))
# ARMLoops: the bounded-guard corollary
t = (wt / (P + 'Machines/ARMLoops.lean')).read_text()
t, blk = cut(t, '/-- **A bounded halting run of a block, inside a larger machine**', '/-- A run whose end configuration is rewritten along an equation. -/')
blk = 'section EmbedSealed\n\n' + seal(['AHalt', 'AReach', 'PreS', 'Ins.embed', 'astep', 'arun']) + '\n' + blk + 'end EmbedSealed\n'
jobs.append(('ARMLoopsSealed', tail_append(t, '\n' + blk, '\nend Complexity.LogProg\n')))
# SavitchARM/Machine: A_noVal (already last; its own file's table only)
t = (wt / (P + 'SavitchARM/Machine.lean')).read_text()
a = '\n/-- The Savitch machine has no input-format check'
assert t.count(a) == 1
t = t.replace(a, '\nsection NoValSealed\n\n' + seal(['astep', 'arun', 'AHalt', 'AReach', 'PreS', 'Ins.embed']) + a, 1)
t = tail_append(t, 'end NoValSealed\n', '\nend SavitchARM\n\nend Complexity.LogProg\n')
jobs.append(('MachineSealed', t))
for name, text in jobs:
    (out / (name + '.lean')).write_text(text)

# controls
union = ['astep', 'arun', 'callSegs', 'vword', 'argSegs', 'Mode.seg0', 'ValidPlain', 'ValidPair', 'plainWord', 'pairWords', 'AHalt', 'AReach', 'PreS', 'Ins.embed']
recursive = ['vword', 'argSegs']
hdr = (wt / 'SavProbe/ctl_header.lean.part').read_text()
body = ''.join(f'#ctl_rfl {NS}{n}\n' for n in union) + ''.join(f'#ctl_eqn {NS}{n}\n' for n in recursive)
for kind, pre in (('unsealed', ''), ('sealed', seal(union))):
    (out / f'SealControl_{kind}.lean').write_text(hdr + '\nsection Controls\n\n' + pre + '\n' + body + '\nend Controls\n')
print('ok', [j[0] for j in jobs])
