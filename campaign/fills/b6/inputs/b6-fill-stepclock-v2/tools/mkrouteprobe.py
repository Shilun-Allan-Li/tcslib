"""Stitch the B6-F1 v2 route probe: one Lean file that stands for the module stack SymbolLift
(with the promoted field lemmas), CounterLoop (with the promotions), StepClock (with the v2 home
block and glue), followed by the route obligations and their axiom prints. Lean cannot import an
edited module without an olean, and no olean is written, so the edited modules are inlined.

Usage: python3 -I mkrouteprobe.py <CounterLoopOverlay.lean> <StepClockOverlay.lean>
                                  <sl-fields.lean.txt> <routechecks.lean.txt> <out.lean>

Layout (each part asserted):
  imports    CounterLoop's own imports (its SymbolLift import is the snapshot's, unedited);
  Part A     the SymbolLift promotion block, verbatim, inside `namespace Turing`;
  Part B     CounterLoop's overlay after its imports, verbatim;
  Part C     StepClock's overlay after its one import (`Build.CounterLoop`), verbatim;
  Part D     the route obligations, verbatim, then the axiom prints.
Inlining makes CounterLoop's private names visible to Parts C and D, which a module boundary would
hide: `routescan.py` checks that neither the home block nor the obligations name one."""
import sys, hashlib, re

cl_p, sc_p, sl_p, rc_p, out_p = sys.argv[1:6]
read = lambda p: open(p, encoding='utf-8').read()
CL = read(cl_p).split('\n'); SC = read(sc_p).split('\n')
SL = read(sl_p).rstrip('\n'); RC = read(rc_p).rstrip('\n')

def split_imports(L, what):
    idx = [i for i, l in enumerate(L) if l.startswith('import ')]
    assert idx and idx == list(range(idx[0], idx[-1] + 1)), (what, 'imports not contiguous')
    assert all(not l.startswith('import ') for l in L[idx[-1] + 1:]), what
    return L[idx[0]:idx[-1] + 1], L[idx[-1] + 1:]

cl_imp, cl_body = split_imports(CL, 'CounterLoop')
sc_imp, sc_body = split_imports(SC, 'StepClock')
assert sc_imp == ['import TCSlib.Complexity.TuringMachine.Build.CounterLoop'], sc_imp
assert 'import TCSlib.Complexity.TuringMachine.SymbolLift' in cl_imp

names = re.findall(r'^theorem (\S+)', RC, re.M)
axioms = ['', '/-! ### Axiom prints -/', '', 'namespace Turing']
for n in (['counter_dec_spec', 'counter_dec_zero', 'counter_word_decrement', 'decrementTM_tr_input',
           'decrementTM_tr_action', 'counterWord_zero',
           'counterOverhead_zero', 'counterOverhead_succ', 'lastEmb_apply',
           'Cfg.decodeSymbols_state', 'Cfg.decodeSymbols_inputPos', 'Cfg.decodeSymbols_workTapes',
           'Cfg.decodeSymbols_workTapePos', 'Cfg.decodeSymbols_output', 'Cfg.liftOver_state',
           'Cfg.liftOver_inputPos', 'Cfg.liftOver_workTapes', 'Cfg.liftOver_workTapePos',
           'Cfg.liftOver_output', 'sc_decExit_injective', 'sc_agree', 'sc_layout', 'sc_lastLayout', 'sc_dec_inputPos',
           'sc_wordPatch_self', 'sc_wordPatch_twice', 'sc_wordPatch_frame', 'sc_stop_step',
           'sc_body_step', 'sc_debit', 'sc_finish', 'sc_timeout', 'exists_stepClockTMVia',
           'exists_stepClockTM'] + names):
    axioms.append(f'#print axioms {n}')
axioms.append('end Turing')

out = (cl_imp + ['',
       '/-! # B6-F1 v2 route probe (stitched; see tools/mkrouteprobe.py) -/', '',
       '/-! ## Part A: the SymbolLift promotion block -/', '', 'namespace Turing', '']
       + SL.split('\n') + ['', 'end Turing', '', '/-! ## Part B: CounterLoop, promoted -/']
       + cl_body + ['/-! ## Part C: StepClock, the v2 overlay -/'] + sc_body
       + ['/-! ## Part D: the route obligations -/', ''] + RC.split('\n') + axioms)
text = '\n'.join(out) + '\n'
# the parts are present verbatim and in order
pos = 0
for part in [SL, '\n'.join(cl_body), '\n'.join(sc_body), RC]:
    k = text.find(part, pos); assert k >= 0, 'part missing'; pos = k + len(part)
open(out_p, 'w', encoding='utf-8').write(text)
sha = lambda s: hashlib.sha256(s.encode('utf-8')).hexdigest()
print(f'route probe: {text.count(chr(10))} lines, sha256 {sha(text)}; {len(names)} obligations '
      f'named, {len(axioms) - 5} axiom prints')
