<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: split_multilinear_at_half_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Splitting a multilinear polynomial at degree `n / 2`

**Claim.** Let `ω ≠ 0` in a field `K` and `c : Finset (Fin n) → K`. There exist
`P₁ P₂ : MvPolynomial (Fin n) K`, both of total degree `≤ n / 2`, such that for every
`x : rootCube ω n`,
`(squarefreePolynomial c).eval x.1 = P₁.eval x.1 + (∏ i, x.1 i) * P₂.eval (fun i => 1 + ω⁻¹ - ω⁻¹ * x.1 i)`.

**Proof.** Split the subsets by `low = {s | s.card ≤ n / 2}` and `high` its complement
(both via `Finset.filter`), with `term s = C (c s) * squarefreeMonomial s`. Take
`P₁ = ∑_{s ∈ low} term s` and `P₂ = ∑_{s ∈ high} C (c s) * squarefreeMonomial sᶜ`, then
`refine ⟨P₁, P₂, ?_, ?_, ?_⟩`.

1. `deg P₁ ≤ n / 2`: `MvPolynomial.totalDegree_finsetSum_le` reduces to one summand;
   `MvPolynomial.totalDegree_mul` plus `squarefreeMonomial_totalDegree_le_card` and
   `Nat.add_le_add_left` give `≤ 0 + s.card`, and membership in `low` gives `s.card ≤ n / 2`.
2. `deg P₂ ≤ n / 2`: same shape, but on the complement. From `¬ s.card ≤ n / 2` and
   `Finset.card_compl` (`(sᶜ).card = n - s.card`), `omega` yields `(sᶜ).card ≤ n / 2`.
3. Evaluation identity. Write `y i = 1 + ω⁻¹ - ω⁻¹ * x.1 i`; `rootCube_affine_inverse` gives
   `y i = (x.1 i)⁻¹` (`hy`). `Finset.sum_filter_add_sum_filter_not` gives
   `P₁ + highPoly = squarefreePolynomial c` (`hpartition`). For the high part, a `calc` with
   `Finset.sum_congr` rewrites each term using `rootCube_top_mul_compl_inverse` and `hcomp`
   (`Finset.prod_congr` with `hy`), then `simp [P₂, squarefreeMonomial, Finset.mul_sum]`
   pulls the top monomial out of the sum. Finally `rw [hpartition]` and `simp` split
   `eval` over the sum.

**Remark.** `split_multilinear_at_half_degree_direct` is the version whose second factor is
already a genuine polynomial in `x` rather than a polynomial evaluated at the substituted
point; that is the form used downstream.
