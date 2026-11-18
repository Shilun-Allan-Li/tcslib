# Wee20.Linear.rec_matrix_eq proof draft

Status: exact-header replacement, inspected but not elaborated. No live source edits,
Lean, lake, build, or Git commands. No new helper declarations or imports.

## Deliverable

`LinearRecMatrix.lean.inc` replaces only the admitted body of `rec_matrix_eq`, currently
`Wee20/LinearCorrect.lean:64`. A Python textual assertion matched its complete existing
header through `:=`. One tactic block, no new admitted terms, maximum line width 100.

## Proof route

Write K for the matrix expression already in the statement and r for its reconstruction
vector (these are explanatory names, not added Lean definitions). For each draw index i,
apply `PG.reconstruct` at zero private input and the single-unit draw `Pi.single i 1`.
The published garbling readers and `Sum.elim_comp_inl_inr r` split its dot product into:

`dotProduct (fun j => 0 - Pi.single i 1 (inr j)) (r composed with inl)
  + (K *v (r composed with inr)) i = 0`.

The matrix coefficient is obtained by `dotProduct_mulVec` and
`single_one_dotProduct`, rather than by expanding any matrix multiplication or sums.
Then split the sum-type draw index:

- Auxiliary index `inl a`: the first block is zero by `Pi.single_eq_of_ne` and
  constructor disjointness. The matrix coefficient is therefore zero.
- Output index `inr j`: `Sum.elim_zero_single` restricts the single draw to the
  matching output basis vector. `neg_dotProduct` and `single_one_dotProduct` give
  `-r(inl j) + (K *v rM)(inr j) = 0`. The existing
  `eq_of_neg_add_eq_zero` transports this to coefficient equality, and the preceding
  `rec_output_eq_eval` identifies that output reconstruction coordinate with evaluation.

All finite-index cases, including an empty output index type, are handled by the
same sum-type case split. No dimension nonemptiness or efficiency hypothesis is added.
No source-group exponent witness, sampler, or algorithm is introduced.

## Dependencies and pending native points

- `PartialGarbling.Raw.reconstruct`, `Raw.pgb_eq`, and `PartialGarbling.pgbCore_eq`
  are the only PG laws/readers used. No foreign definition is explicitly unfolded.
- Lean core `Init/Data/Sum/Lemmas.lean:122`: `Sum.elim_comp_inl_inr` splits r without
  a new local or public vector lemma.
- `Mathlib/Data/Matrix/Mul.lean:123`: `sumElim_dotProduct_sumElim` splits the dot product.
- Same file :710: `dotProduct_mulVec`; :205: `single_one_dotProduct`; :108:
  `zero_dotProduct`; :216: `neg_dotProduct`.
- `Mathlib/Algebra/Group/Pi/Basic.lean:214` publishes
  `Sum.elim_one_mulSingle` with `@[to_additive (attr := simp)]`; the additive theorem
  used is `Sum.elim_zero_single`.
- `Mathlib/Algebra/Notation/Pi/Basic.lean:34` publishes
  `Pi.mulSingle_eq_of_ne` with `to_additive`, yielding `Pi.single_eq_of_ne`.
- `Mathlib/Algebra/Notation/Pi/Defs.lean:86` similarly provides `Pi.neg_apply` from
  its declared additive counterpart of `inv_apply`.
- `Mathlib/Algebra/Group/Basic.lean:368` declares `eq_of_inv_mul_eq_one` with
  `to_additive`, yielding `eq_of_neg_add_eq_zero : -a + b = 0 -> a = b`.
- `rec_output_eq_eval` is an existing theorem currently awaiting the root's native
  check of its separate proof draft. This proof depends on that identity; it does
  not independently eliminate that still-admitted live dependency.

These to_additive lemmas are published algebra theorems, not generated defining
equations. Root native validation must check their resolved names/imports and
function-composition/eta matching in the displayed simplifications. No public reader
gap was found by inspection.

## Actual searches and reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

1. Read the current exact header and the PG formulas/law:

   ```sh
   sed -n '47,75p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearCorrect.lean
   sed -n '80,116p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/Defs.lean
   sed -n '294,306p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/Defs.lean
   ```

2. Search for all required algebra interfaces before considering any helper:

   ```sh
   rg -n 'single.*vecMul|vecMul.*single|dotProduct_mulVec|sumElim_dotProduct|Pi\.single.*inr|elim_zero_single|elim_single_zero' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Pi/Basic.lean TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption
   rg -n 'elim_comp_inl_inr|comp_elim|elim.*neg|neg.*elim' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/Sum/Lemmas.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Pi/Basic.lean
   rg -n 'neg_dotProduct|dotProduct_neg|sub_dotProduct|dotProduct_sub|single_apply.*inr|single_apply.*inl|single_apply_left|single_apply_right' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Pi .lake/packages/mathlib/Mathlib/Algebra/Notation/Pi .lake/packages/mathlib/Mathlib/Data/Sum /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/Sum/Lemmas.lean
   ```

3. Read the found dot-product, sum/single, and inverse/additive-counterpart declarations:

   ```sh
   sed -n '113,135p' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean
   sed -n '775,802p' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean
   sed -n '205,235p' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean
   sed -n '198,229p' .lake/packages/mathlib/Mathlib/Algebra/Group/Pi/Basic.lean
   sed -n '115,128p' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/Sum/Lemmas.lean
   sed -n '25,63p' .lake/packages/mathlib/Mathlib/Algebra/Notation/Pi/Basic.lean
   sed -n '75,90p' .lake/packages/mathlib/Mathlib/Algebra/Notation/Pi/Defs.lean
   sed -n '358,372p' .lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean
   sed -n '504,515p' .lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean
   sed -n '666,675p' .lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean
   ```

4. Further searches for `single_comp`, `comp_single`, `mulSingle_apply`,
   `mulSingle_comp`, `neg_add_eq_zero`, and `neg_add_eq_sub` in Mathlib and Lean core
   located the above public counterparts. Some speculative core Function and
   Algebra/Group/Operations.lean paths did not exist; they provided no dependencies.
   The generic sum/single lemmas obviate a new restriction/coordinate helper.

## Limits and findings

The supplied PG law proves the exact existing statement; no false or unattainable
claim was found. Textual header, line-width, tactic-block count, and absence-of-admission
checks passed. Native elaboration and transitive admission accounting are pending.
