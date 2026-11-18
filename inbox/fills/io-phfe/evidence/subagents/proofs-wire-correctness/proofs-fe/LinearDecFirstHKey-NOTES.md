# Local hKey block in existing Linear.decFirst_correct

Status: inspected proof-only fragment, not natively elaborated. No live source edits,
Lean, lake, build, or Git commands. No public or local helper theorem is added: hT and
hAssoc are local specializations of already-proved public laws. No import or statement
change is proposed.

## Fill artifact and exact local context

`LinearDecFirstHKey.proof.lean.inc` contains only the requested `by` term with every
main tactic indented four spaces, ready for the root's fill_local_proof.py. One tactic
block, no admitted terms, maximum line width 82 columns.

`LinearDecFirstHKey.header.txt` is a read-only context capture of the live hKey header
through `:=`, without a proof body. Python asserted the existing local body was exactly
`:= sorry`. Header SHA-256 at drafting: 2de71d1c149afaabb451be6731df6306e76b50625426ebcdffb563eba15781ad.

The original local j, enclosing theorem header/prose, hCipher proof, and final
cancellation assembly are unchanged. The fragment fills only hKey.

## Exact proof route

Let u = Matrix.vecMul s a.1 for explanation only (no new definition added).

1. Specialize proved `pp.group.groupDot_expVec` at base pp.generator, scalar T column
   `fun i => t.1 i (Sum.inr j)`, and scalar weights u. Read only groupDot_eq and
   expVec_apply at this equality, then commute its scalar dot product. Its RHS is
   the existing scalar `(Matrix.vecMul u t.1 (Sum.inr j))` exponent by ordinary
   Mathlib definitional alignment.
2. Specialize proved `groupVecMul_matMulGroup u a.2.1 M` at output j with congrFun.
   groupVecMul_apply and groupDot_eq expose the exact weighted arbitrary-group
   matrix product on both sides. No scalar matrix witness is introduced.
3. The encCore/setupCore/keyCore readers expose c0 and K1. The proved
   expVec_vecMul reader identifies c0 with expVec g u. The proved arbitrary-vector
   pairVec_expVec_left moves known scalar weights into the existing group action.
4. Matrix.hadamard_apply and expMat_apply read K1's two pointwise factors.
   mul_pow distributes each known scalar power, Finset.prod_mul_distrib separates
   the finite products, and map_mul for the existing monoid hom pp.group.pair g
   separates their pairings. groupVecMul_apply normalizes the RHS group action too.
5. Rewrite the two factors using hT/hAssoc and read pair_pow_right. This is exactly
   the frozen local RHS: the T target-group exponent times the shared W M mask.

The matrix M remains arbitrary group-valued data throughout. The only scalar objects
are the supplied setup/key/encryption draws. No source/target group inversion,
logarithm, encoding inverse, scalar recovery, pair symmetry, or generator-surjectivity
witness is used. No PG reconstruction/privacy/efficiency law is needed.

## Published dependencies inspected

- Linear.lean:setupCore_eq, encCore_eq, keyCore_eq.
- Exponents:358 expVec_vecMul; :514 pairVec_expVec_left; :528
  groupVecMul_matMulGroup; :280 groupDot_expVec. Root reports all these native PASS.
- Exponents:67 groupDot_eq; :85 groupVecMul_apply; :119 expVec_apply;
  :128 expMat_apply.
- Mathlib LinearAlgebra/Matrix/Hadamard:45 hadamard_apply.
- Mathlib Algebra/Group/Basic:216 mul_pow.
- Mathlib Algebra/BigOperators/Group/Finset/Basic:302 Finset.prod_mul_distrib.
- Core/Mathlib map_mul for the already-published pair g monoid hom.
- Mathlib Data/Matrix/Mul:79 dotProduct_comm and the standard scalar vecMul/dot
  definitional alignment, never passed as definitions to simp/rw/unfold.
- Pairing.Group:187 pair_pow_right.

No admitted dependency is required by this local hKey candidate. Full decFirst_correct
standard-only status still requires root integration/native verification of this block
and its enclosing assembly; no such success is claimed here.

## Actual reads and searches

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
sed -n '108,212p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearCorrect.lean
rg -n -A 26 -B 7 'theorem pairVec_expVec_left|theorem groupVecMul_matMulGroup|theorem groupDot_expVec ' TCSlib/Cryptography/Pairing/Exponents.lean
sed -n '1,115p' /private/tmp/io-phfe-drafts/proofs-fe/LinearDecFirstCorrect.skeleton.lean.inc
rg -n -A 4 -B 2 'theorem hadamard_apply' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hadamard.lean
rg -n 'theorem mul_pow|lemma mul_pow|theorem pow_mul' .lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean | head -14
sed -n '237,270p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Linear.lean
sed -n '336,346p' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean
```

The hCipher sibling was read as the native-passed reference for algorithm reader and
pair transport normalization, not edited or duplicated. The proved two generic helpers
close the exact previously reported arbitrary-M gaps; no new helper is necessary.

## Verification limits

Static local-header capture, requested indentation, one-block, width and no-hole
checks passed. Native product normalization, dot/vecMul matching, rewrite-factor order,
and standard-axiom checking remain with the root. No mathematical obstruction found.
