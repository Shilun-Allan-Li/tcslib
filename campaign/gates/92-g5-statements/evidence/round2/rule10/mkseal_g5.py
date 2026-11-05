"""Sealed copies and seal controls for G5's statement PR (rule 10).
Usage: python3 -I mkseal_g5.py <worktree> <outdir>
Each new proof runs under a seal of the other-file TCSlib definitions it could reach:
alphabet_reduction_run (AlphabetReduction), the relabelling section from
FinTM.computesInTime_relabelState to the end of Encoding (the generic lemma, stateEquivFin and the
re-pointed coding steps), exists_code2TM (Codes2Tape), two_work_tapes_binary (TwoTapes; gate 92 finding 1),
universal_TlogT (UniversalTlogT). Controls: a delta and an equation control per sealed definition, unsealed and
sealed (the generic control commands of the earlier gates)."""
import sys, pathlib
wt, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
T = 'TCSlib/Complexity/TuringMachine/'
ERASE = 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg'
def seal(names):
    return ERASE + '\nattribute [local irreducible]\n' + '\n'.join('  ' + n for n in names) + '\n'
RUN = ['Turing.FinTM.ComputesInTime', 'Turing.MultiTapeTM.ComputesInTimeAndSpace',
       'Turing.MultiTapeTM.runFrom', 'Turing.MultiTapeTM.step', 'Turing.MultiTapeTM.initCfg',
       'Turing.Cfg.init']
AR = RUN
EN = RUN + ['Turing.MultiTapeTM.relabelState', 'Turing.Cfg.mapState']
C2 = EN + ['Turing.FinTM.stateEquivFin']
TT = RUN + ['Turing.FinTM.ComputesFunInTime']
UT = RUN + ['Turing.EffectiveMachineCode2.toK', 'Turing.EffectiveCodeK.toFinTM',
            'Turing.EffectiveCodeK.ofSerialize', 'Turing.Code2TM.toFinTM', 'Turing.pairEncode']
def wrap(path, start, stop, names, outname):
    t = (wt / path).read_text()
    assert t.count(start) == 1 and t.count(stop) == 1, (path, t.count(start), t.count(stop))
    i = t.index(start); j = t.index(stop, i)
    t = t[:i] + 'section G5Sealed\n\n' + seal(names) + '\n' + t[i:j] + '\nend G5Sealed\n' + t[j:]
    (out / outname).write_text(t)
wrap(T + 'Robustness/AlphabetReduction.lean', '/-- **Alphabet reduction, run by run**',
     '\nend\n\nend Turing.FinTM\n\n/-! ### Space annotation', AR, 'ARSealed.lean')
wrap(T + 'Encoding.lean', '/-- **Renaming a machine\'s states preserves its computations.**',
     '\nend Turing\n', EN, 'ENSealed.lean')
wrap(T + 'Codes2Tape.lean', '/-- Every two-work-tape binary machine is equivalent',
     '\nend Turing\n', C2, 'C2Sealed.lean')
wrap(T + 'Robustness/TwoTapes.lean', '/-- **Two work tapes suffice** for computing a function',
     '\nend Turing.FinTM\n', TT, 'TTSealed.lean')
wrap(T + 'UniversalTlogT.lean', '/-- **The efficient universal machine**', '\nend Turing\n', UT,
     'UTSealed.lean')
union = sorted(set(AR + EN + C2 + TT + UT))
hdr = (pathlib.Path(__file__).parent / 'ctl_header.lean.part.txt').read_text()
doc = f"""/-
Seal controls for G5's statement PR's rule-10 checks: a delta goal (`#ctl_rfl`) and an equation
goal (`#ctl_eqn`) for each of the {len(union)} definitions sealed in the five sealed copies (the
union). Expected: unsealed, every control passes except recursive definitions' delta goals;
sealed, every control fails. A probe record, not library code.
-/
import TCSlib.Complexity.TuringMachine.UniversalTlogT
"""
ctl = ''.join(f'#ctl_rfl {n}\n' for n in union) + ''.join(f'#ctl_eqn {n}\n' for n in union)
for name, s in (('unsealed', ''), ('sealed', seal(union))):
    (out / f'SealControl_{name}.lean').write_text(doc + hdr + '\n\nsection Controls\n\n' + s + '\n' + ctl + '\nend Controls\n')
(out / 'union.txt').write_text('\n'.join(union) + '\n')
print(len(union), 'sealed definitions')
