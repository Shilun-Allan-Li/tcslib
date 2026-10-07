<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: squarefreeMonomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The squarefree monomial indexed by a subset

**Definition.** For a field `K` and a subset `s : Finset (Fin n)`,
`squarefreeMonomial s : MvPolynomial (Fin n) K` is the product `∏ i ∈ s, X i` of the
variables indexed by `s`, written in Lean as `s.prod (fun i => MvPolynomial.X i)`.

**Remark.** These monomials form the multilinear basis used throughout the Smolensky
split step; the definition is `noncomputable` only because `MvPolynomial` arithmetic is.
