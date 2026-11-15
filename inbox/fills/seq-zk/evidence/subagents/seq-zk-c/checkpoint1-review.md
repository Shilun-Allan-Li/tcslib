# Read-only checkpoint 1 review

Reviewed the lead snapshot
`evidence/snapshots/pre-bootstrap/SequentialZK.lean` in the lead worktree. No edit made.

No mathematical defect found in:
- `seqVerifier_exec_first`, lines 389–421: induction stays before terminal history;
  unchanged cheating prover is correct for phase zero.
- `seqRep_exec_phase_take`, lines 450–470: the earlier real-phase history is an initial
  segment of the final history, including zero-round phases. Core `List.take_drop` has
  the needed `j+i` argument order, so line 469 matches the `j*k+p` prefix bound.
- `seqRep_complete`, lines 482–518: finite probability one suffices pointwise on every
  original tape pair; no independence assumption is needed for completeness. The
  construction also accepts the conjunction over an empty phase list.
- `seqRep_reject_of_first`, lines 527–558: malformed original verdicts do not harm the
  implication. Original `[false]` makes the corresponding conjunction test false.
- `seqRep_sound_first`, lines 568–595: restriction of a uniform verifier tape preserves
  uniformity and keeps prover coins independent.
- `InteractiveProof.seqRep`, lines 724–741: original completeness message bound is
  inherited by the repeated prover; strict soundness follows through domination.

API checks performed:
- Core `List.take_drop`, Init/Data/List/TakeDrop.lean:111, is
  `take i (drop j l) = drop j (take (j+i) l)`.
- Core `List.all_eq_true`, Init/Data/List/Lemmas.lean:551, has the coercion-to-Prop
  characterization required by the proof.
- Core `decide_eq_true`, Init/Prelude.lean:979, accepts a proof of the tested proposition.
- `take_ofFn_castLE` is public at
  `TCSlib/Cryptography/Asymptotic/ReductionSupport.lean:288` and that module is imported
  by the snapshot. It is not a missing Mathlib theorem.
- `Fin.castLE_injective` is public at Mathlib/Data/Fin/SuccPred.lean:86.

No definite failing Lean line is known from read-only inspection. Likely elaboration
pressure points are the width-inferred lambda in the rewrite at line 594 and unused
simp arguments in the false-mover branch near line 421. These are possibilities, not
reported findings. The lead will compile the snapshot after baseline seals.
