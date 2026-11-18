# Local Linear.decSecond_correct hDenominator candidate

Status: scratch proof-only candidate, checked by inspection only. No Lean, lake, build, Git,
or live source edit was run. One tactic block with six-space body, no remaining holes/sorry.
Root must native-check it. No claim that all of decSecond_correct is proved.

## Context compatibility and independence

Paste directly in place of the existing local `hDenominator ... := sorry` in
LinearDecSecondCorrect.skeleton.lean.inc. The original target is unchanged:
`pp.group.pairVec ct.c2 (fun i => sk.R i m) = e(g,g) ^ (mask m).val`.
The fragment uses only aliases sk,ct,R,sa,U,V,X2,mask (some through definitional matching)
and the honest draw parameters. It does NOT use hMix, hMatrix, hNumerator, H, or the pending
kronecker_mul_publicTensor bridge. M remains arbitrary; no scalar witness is introduced.

The only names explicitly unfolded by dsimp are the local let aliases sk and ct. Foreign
algorithms are read via keyCore_eq/encCore_eq/setupCore_eq; exponent representations are read
via published Pairing.Exponents lemmas.

## Proof route

1. keyCore_eq and expMat_apply/expVec_apply identify the actual typed key column sk.R as the
   implicit vector with known scalar column R(_,m).
2. encCore_eq/setupCore_eq expose the actual ct.c2 expression. expMat_mul and two instances
   of expVec_vecMul transport its known scalar action. Reverse expVec_add combines the
   two source-group factors into one implicit scalar row.
3. Matrix.mul_assoc turns (A*U)*X2 into A*(U*X2). Reverse vecMul_add combines the two rows,
   reverse Matrix.mul_add factors A, and reverse vecMul_vecMul obtains sa*(U*X2+V).
4. pair_expVec evaluates the pairing against R(_,m). Its dot product is definitionally
   `Matrix.vecMul (Matrix.vecMul sa (U*X2+V)) R m = mask m`, so rfl finishes.

No generic algebra or transport helper is introduced or duplicated. In particular, the
matrix normalization is performed by existing associativity/distribution lemmas rather
than a coordinate sum reproof.

## Actual reuse searches / reads this invocation

Read the exact local context at lines 28-65 of LinearDecSecondCorrect.skeleton.lean.inc.
Read current live Linear.lean:186-216 and :225-245 for encCore_eq/keyCore_eq, and Exponents.lean
:200-211, :354-384, :428-438 for the exact source-group transport and pairing statements.

Ran these searches (current live worktree, no Git):

* `rg -n 'expVec_add|expMat_mul|expVec_vecMul|pair_expVec|pair_expMat'` over
  Pairing/Exponents.lean and Wee20/LinearCorrect.lean.
* `rg -n 'theorem (vecMul_add|vecMul_vecMul)|theorem.*(dotProduct_mulVec|dotProduct_assoc)'`
  in Mathlib/Data/Matrix/Mul.lean.

Nearest exact reused APIs:

* Pairing/Exponents.lean: expVec_add (204), expVec_vecMul (358), expMat_mul (376),
  pair_expVec (431), expMat_apply and expVec_apply.
* Mathlib/Data/Matrix/Mul.lean: Matrix.vecMul_add (745), Matrix.vecMul_vecMul (818),
  Matrix.mul_assoc and Matrix.mul_add.
* Wee20/Linear.lean: setupCore_eq (176), encCore_eq (200), keyCore_eq (227), with
  record projection normalization by the published equations.

Native-check focus: the sequence uses rw rather than recursive simp for scalar normalization
so that the first matching matrix product/row sum is transformed without expanding the mask
alias or its internal sum. Final rfl uses only the allowed definitional identification of
Mathlib Matrix.vecMul with the displayed dot product and the local aliases.
