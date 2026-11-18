# Finite-product and matrix-action proof candidates

No Lean/lake/build/proof-check or Git command, live edit, extra agent, public helper, import,
axiom or algorithm was introduced. Nine existing headers/docstrings are retained verbatim.
All proof bodies are pure terms with ZERO tactic blocks. Parent elaboration/Rule10 checking
is pending; these are not claimed Lean-passing proofs.

## Route: reuse the finite-sum theorem

The two existing groupDot_expVec{T} proofs create a LOCAL AddMonoidHom

  exponentMap : ZMod B.order →+ Additive B.G       (or Additive B.GT)

with x↦Additive.ofMul(g^x.val). map_zero uses ZMod.val_zero/pow_zero; map_add uses the
PUBLISHED source pow_val_add or the previously supplied pow_val_add_GT candidate.
They then use the existing global `map_sum` (generated from map_prod) and global
`toMul_sum` to get hSum. IMPORTANT: the latter's full name is GLOBAL `toMul_sum`, not
`Additive.toMul_sum`; its source opens Additive rather than declaring that namespace.

hCoordinate uses expVec{T}_apply, pow_mul and published pow_val_mul{_GT}. Finally the
published groupDot_eq reader and Finset.prod_congr combine hCoordinate with hSum.
No finite-set induction, generic product-of-powers lemma, or modular-sum arithmetic theorem
is re-proved. No public exponent-hom helper is needed: the small local structure value is
proof glue and is not an efficient primitive/sampler construction.

## Files/dependency order

1. groupDot_expVec.proof.lean.inc: source bridge, depends only on BASE Group scalar laws.
2. groupDot_expVecT.proof.lean.inc: GT bridge; needs the prior pow_val_add_GT candidate,
   otherwise only the BASE GT multiplication law.
3. expMat_mulVec.proof.lean.inc: source bridge + groupMulVec_apply/expMat_apply/expVec_apply.
4. expVec_vecMul.proof.lean.inc: source bridge + groupVecMul_apply, dotProduct_comm.
5. expMat_mul.proof.lean.inc: source bridge + groupMatMul_apply, Matrix.mul_apply'.
6. expMat_mul_left.proof.lean.inc: source bridge + matMulGroup_apply, dotProduct_comm,
   Matrix.mul_apply'.
7. expMatT_mulVec.proof.lean.inc: GT bridge + target application readers.
8. pair_expVec.proof.lean.inc: GT bridge + pairVec_eq, bilinear_pow, pow_mul, expVec readers.
9. pair_expMat.proof.lean.inc: preceding pair_expVec + pairMat/expMat application readers
   and Matrix.mul_apply'.

All rectangular/finite index orientations match the exact current statements. Source
row-vector action and left matrix action explicitly commute the scalar dot product; right
matrix action uses the natural row/column order. Empty finite index types are supported.
No rank, primality, nonidentity base or efficiency hypothesis is added to these headers.

## Rule10 and proof sketches

Only application/equation readers inspect TCSlib groupDot/expVec/expMat/pairVec/matrix-action
objects. No definition is passed to simp/rw/unfold. Mathlib dotProduct and mulVec/vecMul are
reduced only inside explicit show terms, which is allowed. Matrix multiplication is read
through Matrix.mul_apply'. The local AddMonoidHom and additive type tags are normalized only
inside explicit show terms when map_sum/toMul_sum is applied.

The existing groupDot_expVec proof sketch currently says to induct on a finite sum, but this
candidate uses map_sum instead. Suggested replacement SKETCH ONLY is in
finite-product-sketch-updates.md; public statement/header and opening source prose remain
unchanged. Long bodies visibly name exponentMap,hSum,hCoordinate. Remaining sketches already
match row/column specialization; the pairing sketch can be refreshed to name the GT bridge.

No mathematical obstruction was found. The only remaining uncertainty is unrun Lean
elaboration/instance normalization. Exact?/apply? probes and candidate/local-claim statements
are listed in finite-product-probe-statements.md for the parent; no new helper requires a
frozen-statement repair.
