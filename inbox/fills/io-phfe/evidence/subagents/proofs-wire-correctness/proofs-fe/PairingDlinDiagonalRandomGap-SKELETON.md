# dlinDiagonal_random_gap_le: one-block skeleton after native searches

Status: SCRATCH SKELETON, not a complete proof. Exact searched header/prose byte-preserved.
One tactic block with TWO EXPLICIT TERM SORRIES: hGood and hBadMass. Interval bounds,
pointwise bad-indicator bound and averaging assembly are drafted without admissions, but
none of this skeleton has been native checked. No Lean/lake/build/Git/live edit/extra agent,
new sampler/machine, or Games.Closeness import was used.

## Cycle-free integration home / imports

Recommended home: TCSlib/Cryptography/Pairing/MatrixDH/Diagonal.lean.
Namespace: TCSlib.Cryptography.Pairing (the exact searched helper name stays unchanged).
Native probe imports were Exponents + Games.Probability + OneWayFunctions.Basic. They do not
import Pairing.Linear, so this new child can be imported by Linear for its main random-gap
proof without a Parameters/Linear/MatrixDH cycle. Root owns source installation/facade updates.

The present skeleton uses only that verified target import scope plus existing linarith.
Later hGood filling may need precise Mathlib.Algebra.GroupWithZero.Units.Equiv and
Mathlib.Logic.Equiv.Fin.Basic; hBadMass may use Games.Bridges.Experiments for the published
singleton probability bridge. No such root has been edited here; root checks exact closure.

## What is filled and what remains

Local A is the uniform 3-vector response expectation. Local B is the diagonal-multiplied
2-vector response with independent scalar last coordinate. Local bad is ab0=0 or ab1=0.
All are local proof aliases, not new algorithms/interfaces.

Filled by published APIs:

* hA0/hB0: expect_nonneg (nested twice for B).
* hA1/hB1: expect_mono against constant one and expect_const, using hH1.
* hPoint: on bad, the two [0,1] bounds imply difference at most one; off bad, hGood gives
  equality. The proof uses only classical decision of the bad predicate and linear Real
  arithmetic. It does not weaken the final correction to a union bound.
* hAverage: abs_expect_sub_le_expect on the common ab draw, then exact hBadMass substitution.

Still admitted, explicitly:

1. hGood: for each known nonzero diagonal pair, show A(ab)=B(ab). Use existing Equiv.mulLeft₀
   coordinate permutations + Equiv.piCongrRight. Use Fin.succFunEquiv K 2 and sample-pair/
   sample-equivalence readers to identify the independent pair-plus-last draw with Fin3.
   This is a local subgoal of the natively searched theorem, not a new generic helper API.
2. hBadMass: exactly E_ab 1_{ab0=0∨ab1=0}=2/N-1/N². Reindex ab through finTwoArrowEquiv K,
   evaluate the two independent singleton probabilities with published
   OneWay.uprob_eq_one_div_card 0 (and Bridge.prob_sample_eq_uprob), then expectation linearity
   gives 1/N+(1-1/N)/N. No private counting or cancellation theorem should be re-proved.

These are substantial obligations. They are NOT asserted to be solved by the interval or
averaging assembly. Parent can fill one local block per later invocation after installing
this skeleton and inspecting exact goal states. No extra generic helper proof was supplied.

## Completed native reuse searches (root-run evidence)

Read evidence/search/diagonal-and-parameter-codec/{DlinDiagonalExact,DlinDiagonalApply}.lean.txt,
scope-note.txt, and the run/results.jsonl in the preceding authorized invocation. Exact target
has clean typing, exact? rc1 with exactly one expected no-proof error, apply? rc0 with only
partial suggestions (one sorry, three warnings). No Linear game or future random-gap theorem
was loaded; scope imports only the three independent modules listed above. These are reuse
search results, not proof/skeleton native verification.

## Actual source/API inspection this invocation

Read the exact prior target and native probe source. Re-read Games/Probability.lean:163-175,
:190-204 and :404-419, verifying exact expect_const (174), expect_mono (193), expect_nonneg
(202) and abs_expect_sub_le_expect (409) signatures. Ran a narrow grep for those names to
confirm their public locations. Re-read Equiv.mulLeft₀ (Units/Equiv:30) and
Fin.appendEquiv/succFunEquiv (Logic/Equiv/Fin/Basic:406-416) for remaining subgoal shape.
The full earlier semantic searches and exact counting/reindex references remain in
PairingDlinMatrixRandomGap-DESIGN.md; no native helper reuse result is invented here.

There is no group-valued matrix in this generic field statement, no DLOG/scalar-existence
argument, no sampler preprocessing, and no computational efficiency claim. The exact final
slack/header stay unchanged. Standard-only status awaits both substantive local proofs and
native axiom checks; this artifact is deliberately an admitted skeleton.
