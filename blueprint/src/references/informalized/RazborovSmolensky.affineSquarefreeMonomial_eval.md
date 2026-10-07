<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: affineSquarefreeMonomial_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating the affine-substituted squarefree monomial

**Claim.** For a field `K`, `ω : K`, `s : Finset (Fin n)`, and `x : Fin n → K`,

`(affineSquarefreeMonomial ω s).eval x = s.prod (fun i => 1 + ω⁻¹ - ω⁻¹ * x i)`.

**Proof.** Immediate from `simp [affineSquarefreeMonomial]`: unfolding the
definition, `MvPolynomial.eval` commutes with `Finset.prod` (`eval_prod`, a `simp`
lemma) and each factor is rewritten by the `@[simp]` lemma `affineInvPoly_eval`.

**Remark.** Also `@[simp]`, so evaluations of the substituted monomial normalize
to the explicit product of affine values without further intervention.
