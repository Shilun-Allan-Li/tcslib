"""Sealed copy and seal controls for the configuration-facts API PR (rule 10).
Usage: python3 -I mkseal_cf.py <worktree> <outdir>
CfgFacts' five lemmas run under a seal of the other-file TCSlib definitions they could reach
(`Cfg.inputSymbol`, `Cfg.mapState`), with the usual `simp` erasures. Controls: a delta and an
equation control per sealed definition, unsealed and sealed."""
import sys, pathlib
wt, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
ERASE = 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg'
SEAL = ['Turing.Cfg.inputSymbol', 'Turing.Cfg.mapState']
def seal(names):
    return ERASE + '\nattribute [local irreducible]\n' + '\n'.join('  ' + n for n in names) + '\n'
t = (wt / 'TCSlib/Complexity/TuringMachine/CfgFacts.lean').read_text()
a = '\nnamespace Turing\n'; end = '\nend Turing\n'
assert t.count(a) == 1 and t.endswith(end)
t = t.replace(a, a + '\nsection CfSealed\n\n' + seal(SEAL) + '\n', 1)
t = t[:-len(end)] + '\nend CfSealed\n' + end
(out / 'CfgFactsSealed.lean').write_text(t)
hdr = (pathlib.Path(__file__).parent / 'ctl_header.lean.part.txt').read_text()
doc = "/-\nSeal controls for the configuration-facts API PR: a delta and an equation goal for each sealed\ndefinition. Expected: unsealed, every control passes except recursive definitions' delta goals;\nsealed, every control fails. A probe record, not library code.\n-/\nimport TCSlib.Complexity.TuringMachine.CfgFacts\n"
ctl = ''.join(f'#ctl_rfl {n}\n' for n in SEAL) + ''.join(f'#ctl_eqn {n}\n' for n in SEAL)
for name, s in (('unsealed', ''), ('sealed', seal(SEAL))):
    (out / f'SealControl_{name}.lean').write_text(doc + hdr + '\n\nsection Controls\n\n' + s + '\n' + ctl + '\nend Controls\n')
print(len(SEAL), 'sealed definitions')
