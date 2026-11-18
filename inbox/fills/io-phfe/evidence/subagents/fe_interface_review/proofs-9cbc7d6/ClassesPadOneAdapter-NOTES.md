# Existing Classes.pad_one adapter proof draft

Status: adapter candidate only, not natively elaborated. No live source edits, Lean,
lake, build, or Git commands. No new helper, import, or admitted term in this fragment.
**Its generic expansion dependency remains pending native proof validation.** This is
not a standard-only proof-chain claim and does not establish completed completeness yet.

## Deliverable

`ClassesPadOneAdapter.lean.inc` preserves the entire current frozen docstring, source
tag, sketch and pad_one theorem header. A Python assertion matched the live block,
replacing only its existing admitted body. One tactic block, no explicit holes,
maximum line width 82 columns.

## Exact adaptation and reused interfaces

1. The existing `bidegreeAtMost_iff d 2 P` reader supplies exactly the coefficient-wise
   public/private degree hypotheses of the generic expansion. The predicate itself
   is never unfolded.
2. Apply `PolynomialTensorAlgebra.exists_quadratic_expansion` at `R := ZMod p`, using
   the exact original l,n,d,P. It yields a coefficient family C indexed by a private
   pair and a padded public tuple, fixed before every x,y.
3. The existential PolyTensor witness is
   `fun j tau => C (finProdFinEquiv.symm j) tau`.
   This is the existing canonical row-major product coordinate conversion, without an
   opaque finite enumeration, new runtime algorithm or new tensor encoding.
4. `phfeEval_sum` reads typed PHFE evaluation as nested private-coordinate sums.
   `polyTensorEval_eq` reads its public coefficient sum; `xhat_eq` reads public padding.
   `Equiv.symm_apply_apply` cancels the canonical flattening in every coefficient.
5. `Fintype.sum_prod_type` converts the generic pair sum to nested private sums, and
   `Finset.sum_mul` distributes the two private scalar factors through the public
   tuple sum. The resulting expression is exactly the generic hC x y formula.

No new sum-reindexing/fibre theorem is introduced or re-proved. No generic or class
bundle definition or generated defining equation is explicitly unfolded. The adapter
has no bit-width, encoded-word, prime, invertibility-of-two, nonzero-ring, symmetry,
positive-degree, or positive-variable-count condition. The original statement's
p=1 and l/n/d=0 cases remain included by the generic semiring theorem.

## Explicit pending dependency

At inspection time the live PolynomialTensorAlgebra.exists_quadratic_expansion body
was still `sorry`. Its separate complete candidate in
`PolynomialExistsQuadraticExpansion.lean.inc` is queued for root native checking.
This adapter uses that exact pending theorem. It therefore retains the corresponding
transitive admission until the generic proof is integrated and validated. No
standard-axiom or admission-free status is asserted here.

Other dependencies are already proved public APIs as inspected/reported:

- `Classes.lean:608`, `bidegreeAtMost_iff`.
- `PolynomialTensorAlgebra.lean:88`, exact pending expansion statement.
- `Classes.lean:329`, proved `phfeEval_sum`.
- `Classes.lean:94`, `polyTensorEval_eq`.
- `Classes.lean:76`, `xhat_eq`.
- Mathlib Data/Fintype/BigOperators:253, `Fintype.sum_prod_type`.
- Mathlib Algebra/BigOperators/Ring/Finset:49, `Finset.sum_mul`.
- Published `Equiv.symm_apply_apply` for the existing finProdFinEquiv.

The current live Classes already imports PolynomialTensorAlgebra, so the candidate
needs no import edit. That module remains Mathlib-only and cycle-free below Classes.

## Actual searches and reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
sed -n '1,17p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
rg -n -A 27 -B 6 'theorem pad_one|theorem bidegreeAtMost_iff|theorem phfeEval_sum|theorem polyTensorEval_eq|theorem xhat_eq' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
rg -n -A 17 -B 8 'theorem exists_quadratic_expansion' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PolynomialTensorAlgebra.lean
rg -n 'phfeEval_sum|exists_quadratic_expansion|Fintype.sum_prod_type.*polyTensorEval|polyTensorEval_eq.*sum_mul' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption
sed -n '246,257p' .lake/packages/mathlib/Mathlib/Data/Fintype/BigOperators.lean
sed -n '45,53p' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Ring/Finset.lean
```

The exact generic/class formulas align directly via their published readers and
these two finite-sum equations. No additional helper target was required.

## Limits

Textual frozen header/prose, width, one-block, and no-explicit-hole checks passed.
Root must native-check this adapter after the generic expansion proof, then refresh
admission/axiom inventories. No false statement or mathematical obstruction found.
