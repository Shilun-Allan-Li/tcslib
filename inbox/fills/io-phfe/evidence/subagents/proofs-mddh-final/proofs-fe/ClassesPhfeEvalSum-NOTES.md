# Existing Classes.phfeEval_sum proof draft

Status: inspected exact-header/prose replacement, not natively elaborated. No live source
edits; no Lean, lake, build, or Git commands. No helper or new import is proposed.

## Deliverable

`ClassesPhfeEvalSum.lean.inc` preserves the entire current frozen docstring, source tag,
proof sketch, and theorem header of `phfeEval_sum`. A Python assertion matched that live
block and replaced only its `sorry` body. One tactic block, no admitted terms, maximum
line width 81 columns.

## Proof and exact reuse

1. Read the existing `phfeEval_eq` and `quadEval_eq` to obtain the scalar dot product.
2. A `show` step reads Mathlib's dotProduct as its finite sum by definitional reduction.
   This follows policy's permitted core/Mathlib reduction in a show step: dotProduct is
   never explicitly passed to simp, rw, or unfold, and no new reader is invented.
3. Apply `Equiv.sum_comp` backwards to the existing canonical `finProdFinEquiv`.
   Apply `Fintype.sum_prod_type` to turn the resulting product-type sum into the two
   displayed finite sums. No reindexing machinery is re-proved.
4. Read `privateTensor_eq` and the published `Matrix.kroneckerMap_apply` entry lemma.
   `Equiv.symm_apply_apply` cancels the canonical output pair conversion.
5. The scalar term is now `(y j * y k) * polyTensorEval ...`. Standard commutative
   multiplication lemmas (`mul_comm`, `mul_left_comm`, `mul_assoc`) put it in the
   displayed coefficient-first order.

No tensor roundtrip, fixed-width encoding, source-group exponential theorem, decoder
bridge, prime assumption, or admitted Classes theorem is used. The identity holds over
all positive moduli (including p=1), all degrees (including d=0), and n=0 (empty sums).

Exact source interfaces inspected at preparation time:

- `Classes.lean:291`, `phfeEval_eq`.
- `Classes.lean:279`, `quadEval_eq`.
- `Classes.lean:265`, `privateTensor_eq`.
- `Mathlib/Data/Matrix/Mul.lean:65`, the dotProduct definition, read only for the
  permitted definitional show step.
- `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:712`, Equiv.prod_comp with its
  declared additive theorem `Equiv.sum_comp`:
  `sum i, g (e i) = sum j, g j`.
- `Mathlib/Data/Fintype/BigOperators.lean:253`, the published additive theorem
  `Fintype.sum_prod_type`: sum over pairs equals the nested sum.
- `Mathlib/LinearAlgebra/Matrix/Kronecker.lean:60`, `Matrix.kroneckerMap_apply`.
- Canonical `finProdFinEquiv` at `Mathlib/Logic/Equiv/Fin/Basic.lean:325`;
  only its inverse reader is used, not its definition.

The existing import closure already provides these finite-sum and matrix APIs. The
same exact reindexing pair occurs in the published project proof
`Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean:226`, and also in
`TrapdoorFunctions/Lossy/Gadget.lean:219`; no code or private helper was copied from them.

## Actual search/read record

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
rg -n -A 18 -B 12 'theorem phfeEval_sum|theorem privateTensor_eq|theorem quadEval_eq|theorem phfeEval_eq' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
sed -n '62,82p' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean
sed -n '243,265p' .lake/packages/mathlib/Mathlib/Data/Fintype/BigOperators.lean
rg -n 'finProdFinEquiv\.sum_comp|sum_comp.*finProdFinEquiv|Fintype\.sum_prod_type|Equiv\.sum_comp' TCSlib/Cryptography/AdvancedEncryption TCSlib/Cryptography/Pairing TCSlib/Cryptography/Encoding .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix | head -65
rg -n -A 10 -B 4 'theorem Equiv.sum_comp|lemma Equiv.sum_comp|theorem sum_comp \(' .lake/packages/mathlib/Mathlib/Algebra/BigOperators .lake/packages/mathlib/Mathlib/Data/Fintype | head -70
rg -n 'theorem.*dotProduct|lemma.*dotProduct' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean | head -45
rg -n 'dotProduct_eq|dotProduct.*sum|sum.*dotProduct|dotProduct.*finProd|dotProduct.*reindex' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix .lake/packages/mathlib/Mathlib/Data/Matrix TCSlib/Cryptography/Pairing/Exponents.lean | head -70
sed -n '217,235p' TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean
sed -n '672,713p' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean
rg -n '← .*\.sum_comp, Fintype.sum_prod_type|Fintype.sum_prod_type.*mul_assoc|privateTensor_eq.*kroneckerMap_apply' TCSlib .lake/packages/mathlib/Mathlib | head -28
```

An initial speculative BigOperators/Group/Finset/Equiv.lean path did not exist;
the actual sum_comp declaration is the additive counterpart at Defs:712. The
Mathlib `dotProduct_eq` theorem found in LinearAlgebra/Matrix/DotProduct concerns vector
extensionality against all tests, rather than a finite-sum equation; it is not used.
The allowed show step avoids creating or unfolding a dotProduct reader.

## Validation limits

Static frozen prose/header equality, width, one-block count, and absence-of-admission
checks passed. Native elaboration, standard-axiom checking, and inventory refresh remain
with the root. No missing generic reindexing API, false claim, or mathematical obstruction
was found.
