# game1_good_eq_game2: deterministic rank-good ladder

Candidate: game1_good_eq_game2.ladder.lean.inc, 76 lines, exactly ONE tactic block,
with ONE explicitly isolated local algebra admission hReconstruct. Frozen header,
opening prose and proof-sketch bytes are unchanged. No Lean/lake/Git/native command
or live edit was run. The complete theorem and the surrounding ladder have not been
natively checked; no standard-only axiom claim is made.

## Actual semantics checked

LinearSecurity/Games.lean:45-78,80-108 gives the actual mode branches. Modes 1 and 2
both call maskedCipher at the same expVec(generator,st.c); they differ only in honest
keyCore versus decomposedKey. Both use the SAME keyAt lookup, query.fn, query.matrix,
setup draw, full omega, adversary coin list r, total A.budget.eval kappa, empty history,
and initial SAState(none,0). No tape, seed, padding, or unused simulator draw is changed.
The source's retained simKeyAt let is unused in both selected modes.

runGameDet_eq at Games.lean:167 gives the exact filter and deterministic run. Mode 1
with filtered=false never filters. Mode 2 with filtered=true filters exactly H.det=0.
The ladder derives those exact two run forms using simSetupCore_eq, then splits only
the SAME original rank event. The bad branch returns false on both sides. The good
branch establishes H inverse-times-H=1 by published Matrix.nonsing_inv_mul.

Protocol refusals remain identical: protocolHandler_challenge/key (Data.lean:140/152)
retain the accepted challenge, key-used count, before-challenge refusal, repeated
challenge refusal, and total-budget cap. The proof never changes histories or next
moves. Equality of complete handlers then implies equality of runDet by congruence,
so no additional run interpreter or random coupling theorem is needed.

## One remaining mathematical target

hReconstruct is an arbitrary GROUP-matrix identity under the known scalar inverse:
combineRows C a (matMulGroup A-transpose K) (groupVecMul c K) = K,
where C/a are the first-two/final columns of the computed H inverse and
H=(A|c)^T. J is any Type: no Fintype J or positive output-dimension hypothesis is
needed. The ladder proves the inverse identity hInvMul before exposing this hole.

This target is genuine and sufficient: decomposedKey_eq reduces each key to exactly
three applications of it, retaining the honest R block. gameHandler_eq then gives
identical handlers for every query and state; runDet uses the same unchanged budget.
The supplied hReconstruct is local to the existing theorem, not a new public helper
or additional assumption in its frozen statement.

Before proving a NEW reusable helper, root should natively probe this exact shape
with a generic A,c,K, inverse defined as (basisMatrix G kappa pp A c)^(-1), and the
minimal hypothesis IsUnit(basisMatrix G kappa pp A c).det. Natural cycle-free home
is LinearSimulator after combineRows_eq: that module already owns basisMatrix and
combineRows, and Keys/Games import it downstream. No new runtime definition or import
is needed. No new helper proof is supplied in this invocation.

## Searches and whole public reuse

Static full-name/conclusion searches found no combineRows reconstruction theorem,
no decomposedKey/keyCore identity, and no groupVecMul-single theorem in TCSlib.
Nearest public results actually inspected:
- Pairing/Exponents.lean:528 BilinearGroup.groupVecMul_matMulGroup: known scalar row
  actions compose on an ARBITRARY source-group matrix; consume whole.
- LinearSimulator.lean:122 basisMatrix_eq; :242 combineRows_eq; :193 simSetupCore_eq.
- LinearSecurity/Keys.lean:75 decomposedKey_eq.
- Games.lean:80 gameHandler_eq and :167 runGameDet_eq.
- Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:211 nonsing_inv_mul; its whole
  unit-determinant inverse theorem is already consumed by the ladder.
- Mathlib/Algebra/BigOperators/Fin.lean:80 Fin.prod_univ_castSucc: splits Fin3 into
  Fin2 and the final coordinate; use whole to join the combineRows products.
- Mathlib scalar matrix action, identity-coordinate and product-single APIs should
  close the identity-row action after the existing composition law. Do not re-prove
  a generic finite-product interchange or matrix inverse theorem.

The prospective proof route is to read combineRows/basisMatrix, use the EXISTING Fin3
product split to identify the expression with an inverse-basis group row action, then
use groupVecMul_matMulGroup and hInvMul. Remaining identity-coordinate products should
use existing Finset product/single laws. All group arithmetic is products and powers
by KNOWN scalars. No group-to-scalar inverse, DLOG, sampler, or algorithm is constructed.

Technical elaboration repair surface: simpa's normalization of the fixed Fin6 Boolean
filters and the let-bound ctx, and simp's dependent key-record eta. The sole intended
mathematical hole is hReconstruct; root should keep any such elaboration repair separate
from that local algebra obligation.
