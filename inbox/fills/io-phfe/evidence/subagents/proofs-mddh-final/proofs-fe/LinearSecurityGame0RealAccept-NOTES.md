# LinearSecurity.game0_real_accept

Scratch-only exact frozen doc/header replacement. One4-line tactic block; no admissions,
new public/private helper, import or live edit. No Lean/lake/build/Git command was used.
Native check pending. M0 prose, proof sketch, binders and conclusion are unchanged.

## Exact scope: padded versus fresh laws

This existing theorem compares TWO PADDED presentations. Both game_eq and saGame_eq draw
exactly the same pp, the same SecurityDraw tape and the same adversary coins. The first
uses runGameDet(mode=0,filtered=true), the second mode=0,filtered=false. runGameDet_eq
shows their only difference is the optional bad-basis filter. At mode zero its closed
predicate `decide(2≤mode.val)` is false. Thus the two deterministic runs coincide at every
fixed shared draw, without changing ANY handler or adaptive-query behavior. The pure
reader proof equates the full games beneath the same accept constant; it does not read
accept/probability through definitional unfolding.

In contrast, freshSaGame in Fresh:126 samples setup and then the actual fresh enc/key
or simulator calls at accepted queries. Endpoint.saGame_eq_freshSaGame:55 is the separate
substantive adaptive-resampling acceptance-law theorem and remains an admission in the
source read this invocation. This candidate neither invokes nor proves it and makes NO
pointwise equality assertion between fresh and presampled tapes. The fixed-draw equality
used here is legitimate precisely because both sides of THIS frozen statement already
share the same padded sampler and interpreter.

## Actual searches / readers

- Read full LinearSecurity/Games and Endpoint, and inspected Fresh's handlers/game law.
- `rg -n 'theorem .*run|theorem .*Handler|def .*Handler|saGame|fullRank|game_eq'` over
  Data, Games and Fresh. The exact reusable laws are game_eq:190, saGame_eq:210 and
  runGameDet_eq:167. No new relational-run helper is needed for these identical handlers.
- Read Games:155-220: the mode-zero filter is syntactically gated by decide(2≤mode.val),
  independently of ctx, singularity, the current query or transcript. The closed
  numeric/Fin/decidability fact hMode is proved by the permitted core rfl reduction.
- Read Endpoint:1-90 and Fresh:126-153 to confirm the fresh-game distinction and exact
  location/nature of the separate endpoint coupling obligation.
- Searched Bool.and_false / Bool.false_and in TCSlib and Mathlib. Mathlib uses and_false
  at Data/Int/Bitwise:236 and250, and Data/Nat/Bits:166. Verified BOTH exact theorem names
  in the pinned Lean4.25 source Init/SimpLemmas:296 and298; false_eq_true is in Init/Data/Bool:254.
- Two initial inventory attempts used an unneeded shell builtin-location query and a
  default-ignored toolchain source inventory; those gave no useful theorem evidence.
  Corrected direct pinned paths and `rg --files --hidden` located Init/SimpLemmas, whose
  contents supplied the actual name verification. No Lean executable was run.

Every TCSlib definition is read by its existing public equation theorem. Only those
readers plus proved closed/core Bool equations appear in simp. No basisMatrix, handler,
setup, tape lookup, runDet, accept or ProbComp.prob body is unfolded. Scalar/group values,
all original random coordinates and the TOTAL budget are unchanged.

No mathematical obstruction found. Native elaboration/seal/standard-only success is not
claimed by this scratch draft; root should integrate and check only this existing proof.
