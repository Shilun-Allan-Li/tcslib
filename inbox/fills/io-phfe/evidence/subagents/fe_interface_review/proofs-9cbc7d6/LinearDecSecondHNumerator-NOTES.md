# Local Linear.decSecond_correct hNumerator candidate

Status: scratch proof-only block; inspection only, no Lean/lake/Git/build/live edits. One tactic
block, no hole/sorry in the final fragment, six-space body as requested for the existing
outer proof whose local haves are indented four spaces. Root must native-check integration.
This does not claim that decSecond_correct is complete: hMix/tensor bridge and hDenominator
remain separate pending obligations in the supplied skeleton.

## Exact context compatibility

Paste this fragment in place of `sorry` after the existing local `have hNumerator ... :=` in
LinearDecSecondCorrect.skeleton.lean.inc. It uses precisely the existing aliases T,R,U,V,H,
X,X2,L1m,L0m,sa,value,mask,sk,ct,K, the local coordinate m and local hMatrix. No signature,
header, docstring, or public declaration is changed. The three names in `dsimp only [ct,K,sk]`
are local let aliases; all foreign algorithms are read through encCore_eq/setupCore_eq/
keyCore_eq. No foreign definition or generated equation is explicitly unfolded.

The local hColumn is the concrete column equality obtained from hMatrix, not a new generic
helper: expMat_apply/expVec_apply and pow_val_add transport each scalar matrix entry. After
algorithm readers, expVec_vecMul normalizes c0 and expMat_mul normalizes K. hColumn turns
the second pairing vector into the implicit known scalar column. pair_expVec then evaluates
that pairing. Matrix.vecMul_add and the two reverse vecMul_vecMul applications split its
scalar into the exact existing value/mask aliases. pow_val_add_GT splits the final exponent.

The local hMatrix already consumes hMix, whose intended proof uses the pending
PartialGarbling.kronecker_mul_publicTensor; this dependence is indirect but explicit. M stays
arbitrary group-valued and is never assigned scalar witnesses; its absence from K2/K3 is read
from keyCore_eq, not assumed.

## Actual searches and reused APIs

Read the complete supplied LinearDecSecondCorrect.skeleton.lean.inc and the earlier now-passed
LinearDecFirstHKey.proof.lean.inc for layout/reader conventions. Read current live Linear.lean
around 165-294 for setupCore_eq, encCore_eq, keyCore_eq and exact K2/K3 shapes.

Ran these name searches in the current live worktree (no Git):

* `rg -n '^theorem (expMat_mul|expVec_vecMul|expVec_add|pair_expVec|expMat_add)|^theorem.*vecMul' Pairing/Exponents.lean`
* `rg -n 'vecMul_(add|mul|vecMul)|add_vecMul|vecMul.*add' Mathlib/Data/Matrix/Mul.lean`
* `rg -n 'expMat.*add|expVec.*column|pair_expVec|vecMul_add' Pairing Wee20/LinearCorrect.lean`
* `rg -n 'dotProduct_add|dotProduct.*single|dotProduct_mulVec|mulVec_add|add_mulVec' Mathlib/Data/Matrix/Mul.lean`

Narrow source reads inspected the actual shapes:

* Pairing/Exponents.lean: expVec_add (204), expVec_vecMul (358), expMat_mul (376),
  pair_expVec (431), expMat_apply/expVec_apply; the already-published pow_val_add_GT (181).
* Pairing/Group.lean: pow_val_add, as used in the existing source-group vector reader proof.
* Mathlib/Data/Matrix/Mul.lean: vecMul_add (745), vecMul_vecMul (818).

No expMat_add or column helper was found/introduced. The concrete hColumn follows directly
from existing entry readers and the supplied hMatrix, so no new helper search/probe is needed.

## Native-check focus

The final change uses the definitional equality between a column dot product and Matrix.vecMul;
no definition is passed to a rewrite tactic. The reverse associativity rewrites are deliberately
`rw`, not recursive simp: this preserves the existing value/mask aliases instead of expanding
all internal sums. The remaining unchecked details are ordinary local-alias matching and
projection normalization in the three algorithm readers.
