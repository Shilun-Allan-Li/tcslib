# Linear.pi_dec_eq candidate

Status: scratch candidate checked by inspection only. No Lean, lake, Git command, or live edit
was performed for this invocation. The proof has exactly one tactic block and no `sorry`.
Native verification is pending with root. In particular, the dependency `decSecond_correct`
is still admitted/pending; this candidate does not establish a standard-only correctness chain.
The frozen declaration docstring and header are copied byte-for-byte from the live file.

## Proof route

* Read `dec_eq`, then substitute `decFirst_correct` and `decSecond_correct`.
* `Fintype.prod_sum_type` splits the reconstruction product. `rec_output_eq_eval` identifies
  its output coefficients. `groupDot_expVecT`, `pow_val_neg_GT`, and `rec_matrix_eq` show
  that the two scalar-mask products are inverses.
* The leakage factor uses the proved `leak_product`, finite-product commutation, `prod_pow`,
  `pow_mul`, and `pow_val_mul`. Pairing enters only as the published monoid homomorphism:
  `map_prod`/`map_pow` transport the known powers. `M` stays an arbitrary group-valued matrix;
  no discrete logarithm, existence of scalar witnesses, or inverse encoding is used.
* The local `let`s only abbreviate existing scalar matrices/vectors. No helper declaration or
  interface/statement change is proposed.

## Actual reuse searches/read inspections

All searches were in the current live worktree, without Git:

1. `sed -n '185,270p' .../Wee20/LinearCorrect.lean` and
   `sed -n '1,105p' .../Wee20/LinearCorrect.lean` read the exact header and reconstruction laws.
   `sed -n '104,150p' .../Wee20/LinearCorrect.lean` read the now-proved arbitrary-group
   `leak_product` and `decFirst_correct` statement.
2. `rg -n 'theorem (dec_eq|leak_eq)|groupDot_expVecT|sumElim_dotProduct|dotProduct_mulVec|prod_sum_type|elim_comp_inl_inr'`
   over Linear, Exponents and the precise Mathlib files below located the published readers.
   Narrow `sed` reads inspected their exact types.
3. `rg -n 'groupDot.*groupVecMul|groupVecMul.*groupDot|leak_product|theorem.*pow_val_neg_GT|theorem.*pow_val_mul|theorem.*expVecT_apply'`
   over Pairing and Wee20 found the pointwise groupVecMul reader and existing leak formula;
   no complete arbitrary-group Fubini theorem was found. No new helper was needed.
4. Narrow product-hom searches:
   `rg -n 'prod_pow \(|map_pow \('` and
   `rg -n '^(theorem|lemma) (map_prod|prod_mul_distrib|prod_comm)'`
   over the Mathlib Finset/Hom files located the existing product laws.
   An earlier overbroad variant printed annotation/blank lines; that output was truncated,
   then replaced by these narrow searches and source reads.
5. Read `AGENTS.md` and policy.md before writing; preserved the one-block limit and public
   reader rule. No explicit unfolding or generated-equation reader is used.

## Exact dependencies / source locations

* Wee20/LinearCorrect.lean: `rec_output_eq_eval` (line 52), `rec_matrix_eq` (67),
  `leak_product` (101), `decFirst_correct` (123), `decSecond_correct` (184, pending).
* Wee20/Linear.lean: `dec_eq` (296).
* Pairing/Exponents.lean: `groupDot_eq` (near 59), `groupVecMul_apply` (86),
  `expVecT_apply` (137), `pow_val_neg_GT` (192), `groupDot_expVecT` (311).
* Pairing/Group.lean: `pow_val_mul` (218).
* Mathlib/Data/Matrix/Mul.lean: `sumElim_dotProduct_sumElim` (123),
  `dotProduct_mulVec` (710), `neg_dotProduct`, `dotProduct_zero`.
* Mathlib/Data/Fintype/BigOperators.lean: `Fintype.prod_sum_type` (245).
* Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean: `map_prod` (342),
  `Finset.prod_pow` (612); Basic.lean: `Finset.prod_mul_distrib` (302),
  `Finset.prod_comm`.
* Core/Mathlib equations: `Sum.elim_comp_inl_inr`, `Sum.elim_inl`, `Sum.elim_inr`,
  `Pi.neg_apply`, `map_pow`, `mul_pow`, `pow_mul`, associativity/cancellation.

## Native integration focus

The only unchecked elaboration details are ordinary local-alias matching, finite-product
rewriting and the one-step Sum decomposition in hMask. No mathematical obstruction was found.
If root sees hMask leave function-composition syntax, `change` to its beta-reduced RHS or
`simpa only [Function.comp_apply]` can finish using the same published Sum reader.
