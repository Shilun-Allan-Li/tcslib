<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: squarefreePolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A multilinear polynomial given by its subset coefficients

**Definition.** Given a coefficient function `c : Finset (Fin n) → K`,
`squarefreePolynomial c : MvPolynomial (Fin n) K` is the sum over *all* subsets
`s : Finset (Fin n)` of `MvPolynomial.C (c s) * squarefreeMonomial s`, i.e.
`∑_{s ⊆ [n]} c s · ∏_{i ∈ s} X i`.

**Remark.** The sum ranges over the full `Finset.univ` of subsets, so no degree
restriction is imposed here; the degree splitting is done later by filtering on
`s.card ≤ n / 2`.
