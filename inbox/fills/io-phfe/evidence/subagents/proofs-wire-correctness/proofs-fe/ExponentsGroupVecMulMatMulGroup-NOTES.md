# Existing skeleton BilinearGroup.groupVecMul_matMulGroup proof draft

Status: inspected replacement for the searched helper now live with a placeholder.
No live source edits, Lean, lake, build, or Git commands. No further helper/import
or admitted term is proposed; root native elaboration remains pending.

## Deliverable

`ExponentsGroupVecMulMatMulGroup.lean.inc` preserves the full current live docstring,
source tag, sketch and exact searched header. A Python assertion matched that live
block and the archived anonymous exact? target (changing only its declaration name).
One tactic block, no admitted terms, maximum line width 87 columns.

## Central reuse: no new exponent-map proof

The existing proved `B.groupDot_expVec` accepts **any** base `g : B.G`, not only a
specified generator. Set its base to `M k j`, its scalar vector to `fun i => W i k`,
and its second scalar vector to v. It already proves the full modular collection
of each nested known-power product. Therefore no second local additive homomorphism,
map_sum/toMul_sum argument, or repeated pow_val_add/mul proof is required here.
Those laws remain dependencies of the existing shared theorem, as described by the
preserved helper sketch.

Detailed steps:

1. Function extensionality at output column j.
2. Published `groupVecMul_apply`, `matMulGroup_apply`, and `groupDot_eq` expose
   `prod i, (prod k, M k j ^ (W i k).val) ^ (v i).val` on the left.
3. Reverse `Finset.prod_pow` distributes each known outer power.
4. `Finset.prod_comm` interchanges the two finite products. `Finset.prod_congr`
   reduces to one fixed k.
5. A permitted Mathlib `show` step reads `(Matrix.vecMul v W) k` as the scalar
   dot product `dotProduct v (fun i => W i k)`. Matrix.vecMul and dotProduct are
   never passed to simp/rw/unfold.
6. Apply the exact specialization of `groupDot_expVec` above; read its left side
   with `groupDot_eq` and `expVec_apply`. `dotProduct_comm` puts the known scalar
   factors into the row-vector convention on the right.

M remains arbitrary group-valued data in every step. No scalar witnesses for M,
encoding inverse, logarithm oracle, generator-surjectivity argument, or source/target
inversion algorithm is used. No pairing hypothesis beyond the existing B bundle is
needed by the proof. Empty source/intermediate finite index types are handled by the
same finite-product and dot-product identities. No admitted theorem is a dependency.

## Exact published interfaces inspected

- Exponents:85, `groupVecMul_apply`.
- Exponents:104, `matMulGroup_apply`.
- Exponents:67, `groupDot_eq`.
- Exponents:119, `B.expVec_apply`.
- Exponents:280, `B.groupDot_expVec`, fully proved; its local exponent-map proof
  at :282-303 is only inspected, not copied or reproduced.
- Mathlib Algebra/BigOperators/Group/Finset/Defs:612, `Finset.prod_pow`.
- Mathlib Algebra/BigOperators/Group/Finset/Sigma:117, `Finset.prod_comm`.
- Mathlib Data/Matrix/Mul:79, `dotProduct_comm`; the scalar vecMul/dot-product
  definitions are read by permitted definitional normalization in the show step.

All named simp/rw arguments are published equations/theorems. No foreign algorithm
or generated defining equation is explicitly unfolded. Existing Exponents imports
already provide these APIs.

## Native reuse-search prerequisite

Root completed the two arbitrary-group helper probes before this proof:
`evidence/search/arbitrary-group-and-expansion/run/results.jsonl`.
The exact probe had exactly two expected no-proof errors, no typing errors; apply?
gave no full match, with only partial suggestions for this matrix target. The
archived source imports the proved Exponents module without either proposed helper.
This candidate's statement was subsequently installed and natively accepted as a
skeleton, as reported by the parent. Those facts do not constitute a native PASS of
this newly drafted body.

## Actual searches/reads for this invocation

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
rg -n -A 32 -B 8 'theorem groupVecMul_matMulGroup|theorem pairVec_expVec_left|theorem groupDot_expVec ' TCSlib/Cryptography/Pairing/Exponents.lean
sed -n '696,714p' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean
sed -n '604,615p' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean
rg -n -A 6 -B 3 'theorem prod_comm|lemma prod_comm' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean
rg -n 'groupDot_expVec \(M|groupDot_expVec.*fun i|← Finset.prod_pow|rw \[Finset.prod_comm\]' TCSlib/Cryptography/Pairing TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption .lake/packages/mathlib/Mathlib/Data/Matrix | head -30
sed -n '63,87p' TCSlib/Cryptography/Pairing/Exponents.lean
sed -n '96,108p' TCSlib/Cryptography/Pairing/Exponents.lean
sed -n '64,81p' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean
```

These searches found the exact existing groupDot_expVec consumer pattern already
used by expVec_vecMul, confirming that the fixed-base exponent collection should be
reused rather than rebuilt with another local homomorphism. No new helper target
was needed.

## Verification limits

Static header/doc equality, width, one-block, and no-admission checks passed. Native
elaboration, product-rewrite orientation, generic finite-instance normalization and
standard-axiom checks remain with the root. No false statement or mathematical
obstruction was found.
