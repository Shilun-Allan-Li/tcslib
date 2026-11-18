# Diagonal-gap local hBadMass candidate

Status: scratch proof-only fragment, inspection only; native verification pending. No Lean,
lake, build, Git, live edit or extra agent was used. Exactly one tactic block with four-space
body for the existing skeleton, no remaining hole/sorry in this fragment, ≤100 columns.
The main header and local target remain unchanged. Root reported hGood native PASS; the
full diagonal theorem is NOT claimed proved until this last fragment passes integration.

Exact local target:

  E_{ab:Fin2->K} [if bad ab then 1 else 0] = 2/card(K) - 1/card(K)^2,
  with bad ab := ab0=0 or ab1=0.

## Exact probability calculation

Let c=1/card(K). The existing singleton law hZero is a term composition of three PUBLIC
readers: reverse prob_eq_expect, Bridge.prob_sample_eq_uprob, and
OneWay.uprob_eq_one_div_card 0. No singleton counting statement is re-proved.

For fixed a, hInner states the inner zero-coordinate union probability as
c+(1-c)*1_{a=0}. If a=0 the event is certain, so expect_const gives 1; otherwise it is exactly
the published singleton event for b. Only ordinary conditional equations and ring arithmetic
are used. The local hInner := ?_ uses the required swap before its bullet.

Reindex the actual uniform Fin2 vector using (finTwoArrowEquiv K).symm and the public
expect_sample_equiv. Bridge.expect_sample_pair, expect_bind/pure and existing finite-vector
readers turn it into the two independent uniform field draws. Apply hInner, then expect_add,
expect_const, expect_const_mul and hZero. The remaining identity is exactly
c+(1-c)*c = 2/N - 1/N². Nat.cast_ne_zero/Fintype.card_ne_zero give N≠0; field_simp/ring close.
This is the exact union mass INCLUDING the 1/N² intersection correction, not a 2/N union bound.

The fragment uses no H/range/good-law premises except the local K and bad predicate. No
group element, group matrix, sampler, machine, Closeness module, inverse encoder or DLOG is
introduced. All explicit simp/rw entries are published readers or local proof equalities;
the only dsimp names are local aliases c and bad.

## Actual static searches and source references

This invocation read the current LIVE MatrixDH/Diagonal.lean to confirm the hGood integration,
exact local target and four-space body context. Parent independently reported hGood native
PASS with explicit Games.Bridges.Experiments import and no new Mathlib root.

Re-read these exact generic APIs:

* OneWayFunctions/Basic.lean:144, OneWay.uprob_eq_one_div_card, after searching its namespace
  and exact type. This public theorem is consumed, not its private proof material.
* Games/Bridges/Experiments.lean:66, prob_sample_eq_uprob; :80, expect_sample_pair.
* Games/Probability.lean:208, prob_eq_expect; :304, expect_sample_equiv;
  :158, expect_add; :165, expect_const_mul; :174, expect_const.
* Mathlib/Logic/Equiv/Fin/Basic.lean:48, finTwoArrowEquiv, with existing
  finTwoArrowEquiv_symm_apply (confirmed by in-tree Mathlib use in prior search).
* Mathlib/Data/Fin/VecNotation.lean:122, Matrix.cons_val_zero; :234, Matrix.cons_val_one.
* Mathlib/Data/Fintype/Card.lean:280, Fintype.card_ne_zero. Read existing application of
  Nat.cast_ne_zero.2 Fintype.card_ne_zero in Foundations/Probability.lean:111.

The source searches covered singleton/sample/pair probability, expectation linearity,
cardinality cast nonzero and finite-vector projection reader names. A query for an old
Mathlib/Algebra/GroupWithZero/Power.lean path found no file; no result or proof step relies
on that path. The selected proof uses field_simp/ring directly, requiring no inverse-power
helper or new import if already exposed by the established three-module skeleton scope.

Native focus: exact reindexing function shape, finite-vector reader simplification and the
local conditional hInner proof. The imported Bridges.Experiments is already root-integrated
for hGood. No additional generic helper statement/proof or representation change is needed.
