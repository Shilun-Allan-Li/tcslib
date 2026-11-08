<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermiteCoeff_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Coefficient of a Difference

**Claim.** For square-integrable $f$ and $g$, the Hermite coefficient of $f-g$ at any multi-index is the coefficient of $f$ minus the coefficient of $g$.

**Proof.** By definition, the coefficient of $f-g$ is the integral of $(f-g)H_\alpha$. Distributing multiplication gives $fH_\alpha-gH_\alpha$. Both products are integrable: the $L^2$ hypotheses on $f,g$, together with square-integrability of the Hermite function (`hermiteFunction_memLp_two`), imply integrability of each product by Cauchy–Schwarz. Linearity of the integral then gives the difference of the two Hermite coefficients.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_memLp_two`.
