<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: affineSquarefreeMonomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Squarefree monomial after the affine inverse substitution

**Definition.** For a field `K`, `ω : K`, and `s : Finset (Fin n)`,

`affineSquarefreeMonomial ω s := s.prod (fun i => affineInvPoly ω i)`

in `MvPolynomial (Fin n) K`: the product over `i ∈ s` of the affine factors
`1 + ω⁻¹ - ω⁻¹ X i`. It is the image of the squarefree monomial
`squarefreeMonomial s = ∏ i ∈ s, X i` under the coordinatewise substitution
`X i ↦ affineInvPoly ω i`.

**Remark.** These are the building blocks of the substituted low-degree part in
the Smolensky split: on the cube `{1, ω}^n` with `ω ≠ 0` the substitution is
coordinatewise inversion, so `affineSquarefreeMonomial ω s` evaluates to
`∏ i ∈ s, (x i)⁻¹` there.

**Used in.** `affineSquarefreeMonomial_eval`,
`affineSquarefreeMonomial_totalDegree_le_card`, and
`split_multilinear_at_half_degree_direct`.
