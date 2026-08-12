<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: affineSquarefreeMonomial_totalDegree_le_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The affine-substituted squarefree monomial still has degree at most `s.card`

**Claim.** For a field `K`, `ω : K`, and `s : Finset (Fin n)`,
`(affineSquarefreeMonomial ω s).totalDegree ≤ s.card`.

**Proof.** A three-step `calc`.

1. `MvPolynomial.totalDegree_finset_prod` bounds the degree of the product by
   `∑ i ∈ s, (affineInvPoly ω i).totalDegree`, transported through
   `simpa [affineSquarefreeMonomial]`.
2. `Finset.sum_le_sum` replaces each summand by `1`, using
   `affineInvPoly_totalDegree_le_one`.
3. `∑ i ∈ s, 1 = s.card` by `simp`.

**Remark.** The point is that the affine substitution does not inflate degree: a
squarefree monomial of degree `|s|` stays within degree `|s|`, which is what makes
the `n/2 + d` degree accounting in the Smolensky split work.
