# Canonical-base transpose surjectivity candidate

Status: full scratch candidate, NOT natively elaborated / sealed / axiom-checked.
No Lean/lake/build/Git, live edit, process operation, extra agent or native search was run
by this child. Root owns integration/checks. Exact supplied docstring/header preserved.

Candidate: DlinBaseSurjective.lean.inc. ONE tactic block, no term admissions/new helper/
runtime definition, no line over 100 columns. Two refine entry-equality goals have their
following ext/finite-case proofs; native elaboration must verify actual discharge.
No Fintype K, global classical, new sampler or scalar witness for group data is introduced.

## Exact proof structure and reuse

- Apply Matrix.mulVec_surjective_iff_exists_right_inverse, with the canonical transpose
  explicitly supplied as A. This consumes the public generic right-inverse criterion;
  the proof does not rederive the implication from a right inverse to surjectivity.
- If a!=0 use the scalar 3-by-2 right inverse with rows
    (a^-1,-a^-1), (0,0), (0,1).
- If b!=0 use rows
    (0,0), (-b^-1,b^-1), (1,0).
- ext i j and fin_cases enumerate the FOUR entries of the 2-by-2 product. The published
  Matrix.mul_apply and Fin.sum_univ_three read each 3-term product entry. Matrix.transpose_apply,
  Matrix.of_apply, finite-vector cons/head/tail readers and Matrix.one_apply read the two
  matrices and identity. Only the known nonzero scalar is inverted; mul_inv_cancel₀ and
  mul_neg reduce its entries. Arithmetic zero/unit/additive-cancellation readers finish;
  norm_num handles the remaining closed finite-index/numeral conditions.

The exact candidates work in characteristic two as well: inverse cancellation and additive
negation identities are field identities without a restriction on 2. Zero a/b simultaneously
is excluded only by the ORIGINAL disjunction hab. No row-count, finite-field, prime-order
or matrix-image conclusion is added here. This supplies only the hSurj obligation left
in the real-column skeleton; that larger proof is still pending native checks/integration.

## Actual searches / nearest sources

Read the valid native target in evidence/search/dlin-base-surjectivity/
DlinBaseSurjectivityExact.lean.txt. Parent reports exact? one expected cannot-close and
apply? only partial surjectivity wrappers with scratch sorry, no typing errors. Both use
FiniteLinear + Fin.Basic + core LibrarySearch and exclude Linear/Defs/SelfReduction.
No proof of an unsearched additional helper is supplied.

Static rg searches covered:
- mulVec_surjective_iff_exists_right_inverse and left-inverse variants in Mathlib matrix
  modules; exact criterion read at LinearAlgebra/Matrix/NonsingularInverse.lean:322.
- Existing uses of that criterion/right-inverse construction, and rectangular finite matrix
  multiplication identities; mul_fin_two/three were inspected but do not have these
  rectangular 2x3 by 3x2 dimensions, so their generic coordinate reader is used instead.
- Matrix.mul_apply in Data/Matrix/Mul.lean:293; exact field output is sum over Fin3.
- Fin.sum_univ_three is the PUBLIC to_additive result of prod_univ_three at
  Algebra/BigOperators/Fin.lean:115. The existing generic finite sum is not re-proved.
- Matrix.transpose_apply at LinearAlgebra/Matrix/Defs.lean:134 and Matrix.of_apply :83.
- Matrix.one_apply at Data/Matrix/Diagonal.lean:202, plus one_apply_eq/ne variants :206-213.
- Vector readers cons_val_zero/one/two and head_cons/tail_cons at
  Data/Fin/VecNotation.lean:122/234/237/190/194.
- mul_inv_cancel₀ in Algebra/GroupWithZero/Defs.lean:215; ordinary mul_neg and zero/unit
  multiplication/addition readers; no inverse-existence or rank lemma is re-proved.
- fin_cases i/j usage in Matrix/Notation.lean and the direct FinCases import there.
  That module is actually LinearAlgebra/Matrix/Notation.lean; initial exploratory
  Data/Matrix/Notation.lean and Data/Matrix/Defs.lean paths did not exist and were
  corrected using the declarations' rg locations. No conclusion uses missing paths.

All explicit simp-list items are public equation/algebra lemmas. No core/Mathlib or foreign
TCSlib definition is passed to simp/rw/unfold, and no .eq_1-style generated equation is read.
No new import is proposed: this candidate is intended for the exact already-probed scope.
Native focus is finite-literal reductions and the default norm_num availability; this is
candidate code only, with no claimed PASS or standard-only proof chain.
