# Existing Wee20.Linear.leak_product proof draft

Status: exact-header/prose replacement, inspected but not natively elaborated. No live
source edits, Lean, lake, build, or Git commands. No helper or import is proposed.
Parent reports batch dc9fdccf8 with 24 additional standard-only declarations; that is
supplied status, not an independently resolved Git identity here.

## Deliverable

`LinearLeakProduct.lean.inc` preserves the complete current frozen docstring, source
tag, proof sketch, and theorem header. Only its existing admitted body is replaced.
A Python assertion matched the live block before replacement. One tactic block,
no admitted terms, maximum line width 100 columns. The frozen RHS header is already
exactly 100 columns, so the by term starts on the following line rather than extending
or reformatting that header. An initial scratch formatting check caught the over-width
inline-by layout before any proof artifact was written; the delivered fragment fixes it.

## Exact reused APIs and argument order

1. `Wee20/Linear.lean:315`, `leak_eq`, reads the algorithm as
   `groupDot (groupMulVec M (PG.eval ... x)) z`.
2. `Pairing/Exponents.lean:67`, `groupDot_eq`, exposes the product over rows with
   outer exponent `(z a).val`.
3. Same file :76, `groupMulVec_apply`, and then `groupDot_eq` expose the product of
   the row entries raised to the known function-value coordinates.
4. `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:612`, `Finset.prod_pow`,
   is consumed backwards to distribute the row's known power across its finite product.
5. `pow_mul` is consumed backwards to read
   `(M a b ^ eval_b.val) ^ (z a).val` as
   `M a b ^ (eval_b.val * (z a).val)`.
6. `Pairing/Group.lean:218`, `pp.group.pow_val_mul`, is consumed backwards with
   base `M a b`, first scalar `PG.eval ... b`, and second scalar `z a`.
   It converts the natural product exponent to the representative of the modular
   product. `mul_comm` exchanges those two known scalar factors into the frozen
   statement's `z a * eval_b` order.

`Finset.prod_congr rfl` supplies the row and column traversal using the existing
finite product. No product machinery is re-proved. Empty row or column dimensions
are included automatically by these finite-product identities.

## Arbitrary group matrix, no exponent recovery

M is exactly the theorem's arbitrary matrix of source-group elements. There is no
scalar matrix witness, use of generator surjectivity, inverse of an encoding,
discrete logarithm, R-DLOG assumption, or simulator preprocessing step. The modular
power law already holds for every group element, so it applies directly to each M a b.
The only scalars manipulated are the supplied z entries and the supplied PG.eval values.
No partial-garbling reconstruction/privacy/efficiency law is used.

All TCSlib operations are accessed by published readers/projections, with no explicit
foreign-definition or generated defining-equation unfolding. The cited Exponents
readers are proved; the known-power law lives in the pre-existing Pairing.Group API.
No admitted theorem is a dependency of this draft.

## Actual searches and reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
rg -n -A 25 -B 12 'theorem leak_product' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearCorrect.lean
rg -n -A 20 -B 6 'def leak|theorem leak_eq' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Linear.lean
sed -n '46,94p' TCSlib/Cryptography/Pairing/Exponents.lean
sed -n '206,225p' TCSlib/Cryptography/Pairing/Group.lean
rg -n 'prod_pow|pow_prod|prod.*pow.*val|pow_val_mul.*mul_comm|pow_mul.*pow_val_mul|groupMulVec_apply|groupDot_eq' TCSlib/Cryptography/Pairing/Exponents.lean .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean | head -65
rg -n -A 8 -B 3 'theorem Finset.prod_pow|lemma Finset.prod_pow|theorem prod_pow|lemma prod_pow' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Powerset.lean
```

The existing Exponents proof at :300-301 uses the same pow_mul / pow_val_mul
orientation for known exponent products. The published finite-product theorem and
these existing readers suffice; no new helper target or native search is needed
for an additional helper, because none is introduced.

## Verification limits

Textual frozen prose/header equality, line width, single-block, and no-admission
checks passed. Native elaboration and standard-axiom checking remain with the root,
including normalization of the positive-order parameter to pp.group.order. No false
statement, scalar-witness obstruction, or missing public reader was found.
