<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: split_multilinear_at_half_degree_direct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Half-degree split with the substitution folded into the polynomial

**Claim.** Let `ω ≠ 0` in a field `K` and `c : Finset (Fin n) → K`. There exist
`P₁ R : MvPolynomial (Fin n) K`, both of total degree `≤ n / 2`, such that for every
`x : rootCube ω n`,
`(squarefreePolynomial c).eval x.1 = P₁.eval x.1 + (∏ i, x.1 i) * R.eval x.1`.

**Proof.** Identical bookkeeping to `split_multilinear_at_half_degree`, except that the
complement monomials are built from `affineSquarefreeMonomial ω sᶜ` — the product of the
degree-one polynomials `affineInvPoly ω i = C (1 + ω⁻¹) + C (-ω⁻¹) * X i` — so no external
substitution is needed. With `low`/`high`/`term` as before, take `P₁ = ∑_{s ∈ low} term s`
and `R = ∑_{s ∈ high} C (c s) * affineSquarefreeMonomial ω sᶜ`.

1. `deg P₁ ≤ n / 2`: `MvPolynomial.totalDegree_finsetSum_le`, `MvPolynomial.totalDegree_mul`,
   `squarefreeMonomial_totalDegree_le_card`, and membership in `low`.
2. `deg R ≤ n / 2`: same, using `affineSquarefreeMonomial_totalDegree_le_card` in place of
   the monomial bound, with `(sᶜ).card ≤ n / 2` from `Finset.card_compl` and `omega`.
3. Evaluation identity: `Finset.sum_filter_add_sum_filter_not` gives
   `P₁ + highPoly = squarefreePolynomial c`; `rootCube_affine_inverse` (`hy`) identifies
   `1 + ω⁻¹ - ω⁻¹ * x.1 i` with `(x.1 i)⁻¹`; `rootCube_top_mul_compl_inverse` factors out
   the top monomial termwise under `Finset.sum_congr`, and
   `simp [R, affineSquarefreeMonomial, Finset.mul_sum]` recombines the sum into `R.eval x.1`.

**Used in.** `rootProd_approx_implies_all_functions_approx`, where `R` gets multiplied by a
low-degree approximant to the top monomial.
