<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: squarefreeMonomial_totalDegree_le_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A squarefree monomial has degree at most its support size

**Claim.** For every `s : Finset (Fin n)`,
`(squarefreeMonomial (K := K) s).totalDegree ≤ s.card`.

**Proof.** A two-step `calc` after `classical`.

1. `MvPolynomial.totalDegree_finset_prod` bounds the degree of the product
   `∏ i ∈ s, X i` by `∑ i ∈ s, (X i).totalDegree`; `simpa [squarefreeMonomial]` matches it
   against the goal.
2. `simp` evaluates that sum: each `(MvPolynomial.X i).totalDegree` is `1`, so the sum is
   `s.card`.

**Used in.** Both halves of `split_multilinear_at_half_degree` (and its `_direct`
variant), where the low-degree part must be certified of degree `≤ n / 2`.
