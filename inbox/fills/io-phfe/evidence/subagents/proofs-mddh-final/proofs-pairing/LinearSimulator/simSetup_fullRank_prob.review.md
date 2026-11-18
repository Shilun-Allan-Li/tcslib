# Exact simulator setup rank probability: sorry ladder

Exact live frozen header/opening prose preserved. One outer tactic block; precisely TWO
named local term holes: hBasis and hCount. The complete probability reduction between
those holes is written using existing public laws. No Lean/lake/Git command, live edit,
sampler, runtime definition, new public helper, or new Mathlib root is supplied.
This draft is not native-checked; root must first verify surrounding elaboration.

Integration requires the allowed direct lower-layer import:
  import TCSlib.Cryptography.Pairing.MatrixDH.FiniteLinear
No new Mathlib import/root is proposed. The shared prob_sample_matrix_isUnit_eq is now
root-native-PASS and live in that module. This proof does not repeat its unit-subtype,
Units.val range, ambient matrix-cardinality, or GL-count bridge.

## Full reindexing, with all randomness retained

Tail contains W,U,V,w,v in their exact original right-associated order and dimensions.
The EXISTING prodAssoc inverse groups A,c; prodCongr leaves Tail untouched.
For A,c, the EXISTING arrowProdEquivProdArrow inverse makes each (A row,c entry),
piCongrRight applies the EXISTING prodComm + Fin.snocEquiv per row, and piComm
transposes the resulting augmentation. No inverse map or bijection proof is hand-built.
Thus e's first component is exactly (A|c)^T, not just a matrix having the same rank.
The original full uniform draw is reindexed bijectively; there is no resampling,
conditioning, full-rank assumption, or dropped unused coordinate.

The EXISTING basisMatrix_eq and generated equivalence/Fin.snoc readers are the route
for hBasis. A likely short term candidate, subject to root elaboration, is the symmetry
of basisMatrix_eq after reducible normalization of local e/ac/row and the public
Mathlib equivalences; alternatively use their generated application readers. No new
generic coordinate lemma is required.

The existing isUnit_iff_isUnit_det changes the event. Bridge.prob_sample_eq_uprob,
uprob_comp_equiv, and uprob_fst then reindex the full draw and integrate all Tail masks.
This is the probability form of the shared expectation reindex/product law and avoids
creating another sampler or independence theorem. All typeclass instances are the
existing ZMod/group-order, function, matrix, and product instances.

## Exact finite arithmetic hole

hCount is ONLY the specialization of the shared n=3 natural GL count to K=ZMod order
and its rational simplification. It must use ZMod.card, Fin product readers, the
prime-order >=2 bounds for Nat.cast_sub, and public power/cast/rational arithmetic.
Its exact output is (1-1/p)*(1-1/p^2)*(1-1/p^3), never a coarse 1/p or 3/p estimate.
The last rankSlack_eq/ring step is already included. No count or probability theorem
is reproved in this hole.

No mathematical obstruction was identified. Root can first native-check the typed
equivalence and surrounding probability glue, then authorize one local-hole fill at a
time. Remaining admissions are explicitly hBasis and hCount, so no completeness or
standard-axiom-only claim is made.

Static instance-import check: Mathlib.Algebra.Field.ZMod is already reachable through
Linear -> PartialGarbling.Defs -> Encoding.Modular -> Candidates.Arithmetic ->
NumberTheory.Primality -> FieldTheory.Finite.Basic. Thus the proposed generic helper
application introduces no new ZMod field-instance root either.
