# Existing Wee20.Linear.decFirst_correct: exact decomposition and missing shared laws

Status: decomposition skeleton, **not a completed proof**. No live source edits, Lean,
lake, build, or Git commands. Exactly one tactic block is in the scratch skeleton; its
two local term-sorry obligations are explicit and must not be mistaken for eliminated
admissions. The two proposed shared laws are statement-only placeholders for root probes,
not installed helpers and not proof candidates.

## Artifacts

- `LinearDecFirstCorrect.skeleton.lean.inc`: frozen full docstring/header retained,
  with exact numerator/key pairing obligations and the final cancellation assembly.
- `LinearDecFirstCorrect.helper-targets.lean.inc`: exact independently reusable target
  statements, each with proposed natural-language docstring, source tag and proof sketch.

Static checks matched the source header/prose, limited width to 100 columns, and counted
one tactic block. No claim of native elaboration or completed correctness is made.

## Why this is longer than the earlier glue proofs

Current Exponents proves actions and pairing transport when the relevant group matrix
is already a known scalar exponential. Here M is arbitrary in the group. Applying
`expMat_mul_left` or `pair_expVec` directly to M would require scalar witnesses for M,
which the actual source algorithm and theorem deliberately do not provide.

The correct generic laws are known-scalar operations on arbitrary group inputs. The
name/shape searches below found readers and scalar-encoded specializations, but no
published version of either exact arbitrary-input law. Proving them repeatedly inside
source-specific ciphertext/key algebra would duplicate reusable matrix/pairing
infrastructure. The root should probe their anonymous statements before helper proofs.
There is no mathematical obstruction or need to weaken the frozen theorem.

## Two exact shared targets and correct scope

1. `B.pairVec (B.expVec g v) u = B.pair g (groupDot u v)` for arbitrary group vector u.
   This is the small generic pair/product bridge: pairVec_eq, expVec_apply,
   pair_pow_left and map_prod for the already-published monoid hom B.pair g.
2. `groupVecMul v (matMulGroup W M) = groupVecMul (Matrix.vecMul v W) M` for arbitrary
   group matrix M and known scalar v,W. It states exactly the group action needed to
   identify the shared W mask. The full statement is at BilinearGroup B, **not** at
   arbitrary H with only CommMonoid H: reduction of scalar sums/products modulo p uses
   the known order law of B.G. A naive generic CommMonoid-H version would be false
   without an exponent-p hypothesis.

Suggested shared home: beside the existing actions/transport theorems in the owned
`Pairing/Exponents.lean`. No new runtime function, sampler, machine, or efficiency
contract is introduced. Parent may choose names after native exact?/apply? searches.
Requested helper searches=4 (two methods for each target), verified records=0 here.
Use the fully proved current Exponents import, but do not load the target placeholders
or a later theorem admitted on their strength into the search environment.

## Exact source-specific assembly

Let u = s vecMul A and v = u vecMul W (explanatory notation only). For each output j,
the skeleton's exact local statements are:

- Cipher pairing = `pair g (groupVecMul z M j) * pair g (groupVecMul v M j)`.
  Read encCore_eq and setupCore_eq; expVec_vecMul identifies scalar A and AW actions;
  Matrix.vecMul_vecMul identifies s(AW) with (sA)W. The pairing monoid-hom multiplication
  property and Finset.prod_mul_distrib split the existing c1 product. Shared target 1
  turns each known-vector pairing into the displayed group-matrix action.
- Key pairing = `pair g g ^ ((u vecMul T)(inr j)).val *
  pair g (groupVecMul v M j)`.
  Read keyCore_eq, Matrix.hadamard_apply, pairVec_eq and pair multiplicativity. The Tbar
  part is pair_expVec at its existing scalar column. Shared targets 1 and 2 handle
  the W times arbitrary-M part. Public expMat_apply/expVec_apply and a permitted
  Mathlib vecMul/dotProduct show or rfl step identify the existing scalar T output
  coordinate; no new scalar or coefficient identity is necessary.

After those two obligations, decFirst_eq yields `(P*Q)*(E*Q)^-1`. The existing
pow_val_neg_GT reader puts the desired negative scalar exponent into E^-1. Public
mul_inv_rev, associativity and mul_inv_cancel_right cancel Q directly. The skeleton
contains this exact final rw sequence. It only cancels the target-group inverse
already present in decFirst; no source-group inverse algorithm, group-log inverse,
scalar recovery, or new inversion operation is introduced.

## Nearest verified/public APIs inspected

- Linear.lean:setupCore_eq, encCore_eq, keyCore_eq, decFirst_eq.
- Exponents.lean:groupDot_eq:67, groupVecMul_apply:85, matMulGroup_apply:104,
  expVec_apply:119, expMat_apply:128, pairVec_eq:154.
- Exponents.expVec_vecMul:358 and pair_expVec:431 (current proof-source line positions).
- Existing expMat_mul_left:393 assumes a scalar-encoded right matrix, explaining
  why it does not solve the arbitrary-M target.
- Pairing.Group:pair is G ->* G ->* GT (:126), pair_pow_left:183,
  pair_pow_right:187, pow_val_mul:218, pow_val_add:254.
- Mathlib map_prod (Group/Finset/Defs:342), Finset.prod_mul_distrib
  (Group/Finset/Basic:302), Finset.prod_pow (Defs:612), finite product interchange.
- Mathlib Matrix.vecMul_vecMul (Data/Matrix/Mul:818), Matrix.hadamard_apply
  (LinearAlgebra/Matrix/Hadamard:45).
- Exponents.pow_val_neg_GT:192 and Mathlib mul_inv_rev / mul_inv_cancel_right
  (Algebra/Group/Defs:1049,1127) complete the final algebra.

No rec_output_eq_eval, rec_matrix_eq, leak_product, PG reconstruction/privacy, or
realisability/efficiency premise is needed for this first block.

## Actual searches and reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
sed -n '116,160p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearCorrect.lean
sed -n '80,304p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Linear.lean
rg -n '^theorem|^def |^private def|^noncomputable def' TCSlib/Cryptography/Pairing/Exponents.lean
sed -n '142,222p' TCSlib/Cryptography/Pairing/Exponents.lean
sed -n '336,450p' TCSlib/Cryptography/Pairing/Exponents.lean
rg -n '^theorem.*(pair|bilinear|pow_val)' TCSlib/Cryptography/Pairing/Group.lean TCSlib/Cryptography/Pairing/Operations.lean
rg -n 'pair.*(groupVecMul|groupDot)|groupVecMul.*(exp|pair)|pair.*prod|prod.*pair|bilinear.*prod|pair.*expVec_vecMul' TCSlib/Cryptography/Pairing TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix | head -70
rg -n 'vecMul_vecMul|vecMul_add|vecMul_sub|vecMul_smul|vecMul_transpose|dotProduct.*vecMul|vecMul.*dotProduct|fromBlocks|fromCols' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean | head -60
rg -n 'groupVecMul.*matMulGroup|matMulGroup.*groupVecMul|groupVecMul.*assoc|pairVec.*mul|pairVec.*groupDot|pair.*groupDot|groupDot.*pair|groupVecMul.*add' TCSlib .lake/packages/mathlib/Mathlib | head -65
rg -n 'pairVec_expVec_left|groupVecMul_matMulGroup|pairVec_expVec|matMulGroup.*vecMul|groupDot.*pair' TCSlib .lake/packages/mathlib/Mathlib | head -40
rg -n -A 4 -B 2 'theorem mul_inv_cancel_right|lemma mul_inv_cancel_right|theorem mul_inv_rev|lemma mul_inv_rev' .lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean
```

Additional precise reads: Group:25-136,168-204; Exponents:94-109; generic map_prod
Defs:333-351. A speculative Data/Matrix/Hadamard.lean path did not exist; the public
hadamard_apply theorem is in LinearAlgebra/Matrix/Hadamard. Existing project pair hom
uses were also searched; only the underlying map_mul applications were found.

## Next step

Run the two exact helper probe targets in isolation. If no complete existing match is
found, prove one shared helper per invocation, then fill one skeleton obligation per
invocation and native-check the frozen decFirst_correct statement. The decomposition
has no semantic gap; its outstanding work is reusable algebra proof infrastructure.
