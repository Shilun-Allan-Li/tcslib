# One shared GL-count probability header (design only)

The target fragment contains one new theorem header/opening docstring with a term sorry,
for root's isolated native typing/exact?/apply? probes. NO proof has been drafted.
No runtime definition, import line, source edit, Lean/lake/Git command, or new agent.

Proposed full name: TCSlib.Cryptography.Pairing.prob_sample_matrix_isUnit_eq.
Proposed home: existing Pairing/MatrixDH/FiniteLinear.lean, before the smallRows theorem
(or before both existing theorem bodies for a clean isolated source-prefix probe).
Context: namespace TCSlib.Cryptography.Pairing; open TCSlib.Cryptography.Games.
The existing host imports already supply every named API. No new imports are proposed
in the fragment. Host ProbComp.sample accepts Type, so K : Type matches its exact API.

## Exact meaning and scope

For q=Fintype.card K, numerator is the NATURAL product over i : Fin n of q^n-q^i.
Only after that natural product is computed is it cast to Real. Denominator is the
real power q^(n*n), the cardinality of n-by-n matrices. This matches card_GL_field's
counts without silently changing natural subtraction into field subtraction.

There is no positive-dimension hypothesis. At n=0 the empty product and denominator
are both one, and the unique empty matrix is a unit; the formula correctly gives 1.
No source group, prime-modulus schedule, generator, conditioning, or full-rank premise.
Only Field and Fintype are required.

## Existing API composition to probe, not a new proof

- Games.Bridge.prob_sample_eq_uprob converts the existing uniform experiment to uprob.
- Cryptography.uprob_def exposes event-subtype Nat.card / ambient Fintype.card.
- As in the now-proved smallRows square branch, the IsUnit subtype is the range of
  Units.val; Nat.card_range_of_injective Units.val_injective supplies its cardinality.
  Do NOT build a new units/subtype equivalence or re-count the units.
- Matrix.card_GL_field supplies the entire natural product. Matrix.GeneralLinearGroup
  is the existing abbreviation for matrix units, so there is no new GL conversion.
- Fintype.card_fun/card_fin, pow_mul, and Nat.cast_pow normalize ambient matrix count
  to q^(n*n). Do NOT introduce another generic matrix-cardinality lemma.

This helper centralizes the unit-subtype/range/count bridge ONCE. No separate helper
for determinant events or n=2/n=3 is proposed; existing matrix unit/determinant and
surjectivity equivalences cover those interface changes.

## Consumer reuse map

1. FiniteLinear.smallRows_surjectivity_failure_le, r=2:
   use Matrix.mulVec_surjective_iff_isUnit, complement probability via existing
   ProbComp.prob_not (or its existing uprob counterpart), and this lemma at n=2.
   Simplify Fin.prod_univ_two to (q^2-1)*(q^2-q), denominator q^4.
   REMOVE the current local hgood unit-range/card_GL translation and local hall count;
   keep its cast-subtraction bounds and elementary final rational inequality.

2. LinearSimulator.simSetup_fullRank_prob:
   reindex the independently drawn A/c coordinates as the FULL uniform 3-by-3 H,
   integrate untouched masks with existing expectation/product readers, and apply
   this lemma with K=ZMod pp.group.order and n=3. Translate IsUnit H.det via existing
   Matrix.isUnit_iff_isUnit_det; do NOT separately redo the unit-range/card_GL bridge.
   Its exact full-rank fraction is (q^3-1)*(q^3-q)*(q^3-q^2)/q^9, equal to
   (1-1/q)*(1-1/q^2)*(1-1/q^3). This preserves the exact rankSlack and never replaces
   failure by 1/q. Natural-to-real subtraction casts need the usual q>=2 bounds.

FiniteLinear imports only probability/Mathlib support and has no Wee20 dependency.
LinearSimulator currently has NO import path to FiniteLinear (static import-graph
check); root will need to settle that lower-layer dependency when integrating. This
design-only task adds no import. The proposed direction is cycle-free because the
existing FiniteLinear import graph contains no simulator/FE module.

## Required native authorization before proof

Probe the exact target under the CURRENT FiniteLinear import/namespace prefix, before
new helper or consumer bodies. Run native typing, exact?, and apply?; do not count an
import failure as a valid search. The target is not claimed typechecked until root
reports those results. No mathematical obstruction found in the proposed formula.
