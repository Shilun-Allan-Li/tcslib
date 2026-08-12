<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: squarefreeMonomial_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating a squarefree monomial

**Claim.** For `s : Finset (Fin n)` and `x : Fin n → K`,
`(squarefreeMonomial s).eval x = ∏ i ∈ s, x i`.

**Proof.** Immediate from `simp [squarefreeMonomial]`: unfolding the definition turns the
goal into the statement that `MvPolynomial.eval` commutes with a finite product of
variables, which the default simp set already knows.

**Remark.** Marked `@[simp]`, so all later evaluation computations on the cube discharge
this step automatically.
