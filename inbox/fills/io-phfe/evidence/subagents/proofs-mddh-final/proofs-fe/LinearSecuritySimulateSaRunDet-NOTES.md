# LinearSecurity.simulate_saRun_det

Scratch-only exact frozen doc/header replacement. The existing statement remained admitted
in live LinearSecurity/Theorems.lean:105. The candidate contains one4-line tactic block,
no admissions and no helper. No Lean, lake, build, Git or live edit was performed. Native
check pending.

The proof reads the typed adversary run with the exact public SAAdv.run_eq equation and
applies the existing generic simulate_buildComp_detImpl_eq_pure theorem. All arguments
match without a cast or theorem change: next=A.next κ pp pk r, timeout=false,
handler=h, TOTAL query budget=A.budget.evalκ, initial history=[], initial state=s.
The target oracle spec is passed explicitly; the source typed spec is inferred from h.
No run/body definition is unfolded, and no machine or sampler is constructed.

## Static search record / exact dependencies

- Read the full current FE Run.lean and the requested frozen Theorems header.
- `rg -n 'simulate_saRun_det|simulate_buildComp_detImpl_eq_pure|theorem run_eq|def run|simulate_runDet'`
  over Run, LinearSecurity/Theorems and Data. An initially guessed Oracle.lean path did
  not exist; the actual typed adversary implementation is Data.lean.
- `rg -n 'namespace SAAdv|run_eq|def run|structure SAAdv'` over LinearSecurity/Data and
  Wee20 found Data:108. A guessed LinearData.lean file did not exist; all relevant code
  is already in LinearSecurity/Data.lean, which was then read in full.
- SAAdv.run_eq, Data:108: exact buildComp next false (budget.evalκ) [] equation.
  Data imports FE.Run directly, so no new import/root is required.
- simulate_buildComp_detImpl_eq_pure, FE/Run:111: for arbitrary spec/spec', deterministic
  stateful h, budget/history/state, simulation is pure(runDet ...). Its current source
  proof is complete, using only buildComp/runDet case readers and simulation readers.

The exact original docstring, proof sketch, all binders and conclusion were copied
mechanically. The fragment uses public theorem readers only. No semantic obstruction
was found. Native success is not claimed by this scratch replacement.
