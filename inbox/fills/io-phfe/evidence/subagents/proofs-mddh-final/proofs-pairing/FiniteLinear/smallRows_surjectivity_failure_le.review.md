# smallRows_surjectivity_failure_le proof candidate

The exact searched header and complete source proposal docstring are unchanged.
The candidate has one tactic block, no admissions and no new helper declaration.
No Lean, lake, Git, live edit or checker was run. Native validation remains pending.

Root authorized this target from evidence/search/mddh-finite-linear/run2: the
corrected imports typed cleanly, exact?/apply? found no complete match, and no
additional typing errors occurred. Run1 had an invalid import and is not reuse
evidence. The candidate consumes the existing GL count; it does not reproduce a
finite-field counting theorem.

## Import requirement

The valid probe imported Exponents, Games.Probability, OneWayFunctions.Basic,
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card and NonsingularInverse.
This proof additionally uses the precisely named Games.Bridge.prob_sample_eq_uprob
from TCSlib.Cryptography.Games.Bridges.Experiments. If not already transitive,
root should add that exact import to the eventual independent FiniteLinear file.
The scalar/cardinality APIs used below are already dependencies of these matrix
and probability modules; do not import broad Mathlib or a pairing facade.

## Cases and reuse

The only field-size fact is the published Fintype.one_lt_card_iff_nontrivial,
using the existing Field nontrivial instance. Its real cast bounds q below by
one and makes the denominator positive. The published reciprocal-power order
law gives 1/q^2 <= 1/q once, reused by the positive-row cases.

Zero rows: the target vector type Fin 0 -> K is a subsingleton, so any matrix
map is surjective with zero preimage. The existing prob_eq_expect/expect_const
readers reduce failure probability to zero. No counting is required.

One row: failure implies the zero matrix. If entry M i j were nonzero, every
output y has explicit preimage Pi.single j (y i / M i j); mulVec_single and the
existing mul_div_cancel0 law identify it. Fin 1 subsingleton identifies every
output coordinate with i. This is only a scalar proof witness; no group element
is mapped to a scalar or used in an algorithm. uprob_mono bounds failure by the
zero singleton. uprob_def, Nat.card_eq_fintype_card and the public
Fintype.card_subtype_eq count that singleton as one, while Fintype.card_fun gives
q^2 total matrices. The reciprocal bound and nonnegativity give <=2/q.

Two rows: hr forces the remaining natural predecessor to zero. The published
Matrix.mulVec_surjective_iff_isUnit turns good matrices into matrix-ring units.
IsUnit is definitionally membership in Set.range Units.val; a permitted Mathlib
change identifies these predicate types, and the existing
Nat.card_range_of_injective Units.val_injective identifies their cardinality
with GL. Matrix.card_GL_field at n=2 gives (q^2-1)(q^2-q), with the public
Fin.prod_univ_two reader. This avoids creating a new units/subtype equivalence
or re-proving an invertible-matrix count.

The published uprob_not and uprob_def convert the singular probability to one
minus the good fraction. Fintype.card_fun and pow_mul give q^4 matrices. The
natural-subtraction cast readers have explicit q^2>=1 and q^2>=q premises from
one_le_pow0/le_self_pow0, so no truncated subtraction is silently treated as a
ring subtraction. Existing field/ring normalization then reads the exact failure
as 1/q+1/q^2-1/q^3. The shared reciprocal inequality and nonnegativity of 1/q^3
finish <=2/q. The exact field-size hypothesis is retained throughout.

## Native-check risks

- Verify the namespace/import Games.Bridge.prob_sample_eq_uprob. It is not in
  namespace ProbComp; root already encountered this distinction in FE endpoints.
- Check Fintype.card_fun normalization through Matrix's Mathlib abbreviation;
  the candidate uses change to reduce only Mathlib function types, not any
  TCSlib definition body.
- The square-case IsUnit/range change uses the actual Mathlib IsUnit definition
  (exists bundled unit whose value equals M), so the subtype predicates are
  definitionally identical. It does not invent or prove a generic counting lemma.
- Verify `Matrix.card_GL_field (𝔽 := K) 2` and Fin.prod_univ_two reader inference.
- The one-row single-column image uses the canonical MulOpposite scalar action;
  its change should reduce to Mij*(yi/Mij)=yi as written. Use its existing
  application readers if native elaboration requires an explicit pointwise step.
- Check the source placeholder/swap side-goal order and the final small scalar
  field_simp certificate. No fallback counting theorem or new helper is needed
  for the presented mathematical argument.

No mathematical obstruction found. Field order two and r=0 are included. The
probability bound may exceed one for q=2, which is harmless and exactly the
stated target. This is independent finite-field distribution glue, without any
advice/efficiency/DLIN hypothesis or new source-group operation.
