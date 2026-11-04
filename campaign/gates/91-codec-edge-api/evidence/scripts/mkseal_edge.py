"""Sealed copies and seal controls for the codec edge-mode API PR (rule 10).

Usage: python3 -I mkseal_edge.py <worktree> <outdir>
Langs: `mem_edgeLang` (the file's last declaration) runs under a seal of the other-file TCSlib
definitions it could reach. Checks: the edge section (from its heading to the file's end) runs under a seal of the other-file
TCSlib definitions it could reach. Deciders: likewise from `section Edge` to the end. Controls:
one delta control per sealed definition, an equation control for recursive ones.
"""
import sys, pathlib
wt, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
P = 'TCSlib/Complexity/SpaceComplexity/Codec/'
ERASE = 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg'
CO = 'Complexity.Codec.'
LP = 'Complexity.LogProg.'
def seal(names):
    return ERASE + '\nattribute [local irreducible]\n' + '\n'.join('  ' + n for n in names) + '\n'
CHECKS = [CO + n for n in ('W', 'hH', 'cellOf', 'chunkBit', 'cfgWord', 'cfgCode', 'ValidChk', 'edgeLang')]
DEC = ([CO + n for n in ('CA', 'Regs.val', 'Regs.Bd', 'cpDst', 'cpSrc', 'cpNext', 'scDst', 'scSrc',
        'scFactor', 'scNext', 'icReg', 'icCount', 'icNext', 'icL', 'goto', 'bnd', 'orc', 'Shape1',
        'VAcc', 'ValidChk', 'EdgeChk', 'edgeLang', 'W', 'hH', 'cfgCode')]
       + [LP + n for n in ('astep', 'arun', 'PreS', 'AHalt', 'AReach', 'vword', 'callSegs')])
# Checks
t = (wt / (P + 'Checks.lean')).read_text()
a = '/-! ## Edge codes -/\n'
assert t.count(a) == 1
t = t.replace(a, a + '\nsection EdgeSealed\n\n' + seal(CHECKS) + '\n', 1)
end = '\nend Complexity.Codec\n'
assert t.endswith(end)
t = t[:-len(end)] + '\nend EdgeSealed\n' + end
(out / 'ChecksSealed.lean').write_text(t)
# Deciders
t = (wt / (P + 'Deciders.lean')).read_text()
a = 'section Edge\n'
assert t.count(a) == 1
t = t.replace(a, a + '\n' + seal(DEC) + '\n', 1)
t = t.replace('\nend Edge\n', '\n', 1)
assert t.endswith(end)
t = t[:-len(end)] + '\nend Edge\n' + end
(out / 'DecidersSealed.lean').write_text(t)
# controls
# Langs
LANGS = ['Turing.pairEncode', 'Turing.Cfg.InWindow', CO + 'cfgCode']
t = (wt / (P + 'Langs.lean')).read_text()
a = '/-- **Membership in the edge-code language.** -/\n'
assert t.count(a) == 1
t = t.replace(a, 'section EdgeSealed\n\n' + seal(LANGS) + '\n' + a, 1)
assert t.endswith(end)
t = t[:-len(end)] + '\nend EdgeSealed\n' + end
(out / 'LangsSealed.lean').write_text(t)
# controls: a delta goal and an equation goal per sealed definition, unsealed and sealed
union = sorted(set(LANGS + CHECKS + DEC))
hdr = (pathlib.Path(__file__).parent / 'ctl_header.lean.part.txt').read_text()
doc = f"""/-
Seal controls for the codec edge-mode API PR's rule-10 checks, with the generic control commands
of E-Q cont1's review: a delta goal (`#ctl_rfl`) for each of the {len(union)} definitions sealed in the three
sealed copies (the union), and an equation goal (`#ctl_eqn`) for each. Each logs `CONTROL_PASS` or
`CONTROL_FAIL`. Expected: unsealed, every control passes except recursive definitions' delta goals;
sealed, every control fails. A probe record, not library code.
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
"""
ctl = ''.join(f'#ctl_rfl {n}\n' for n in union) + ''.join(f'#ctl_eqn {n}\n' for n in union)
for name, s in (('unsealed', ''), ('sealed', seal(union))):
    (out / f'SealControl_{name}.lean').write_text(doc + hdr + '\n\nsection Controls\n\n' + s + '\n' + ctl + '\nend Controls\n')
print(len(union), 'sealed definitions')
(out / 'union.txt').write_text('\n'.join(union) + '\n')
