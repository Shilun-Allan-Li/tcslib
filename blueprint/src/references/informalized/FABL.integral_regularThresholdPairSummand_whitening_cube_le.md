<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.integral_regularThresholdPairSummand_whitening_cube_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Whitened third moment bound

**Claim.** For $\rho\in(-1,1)$, the expected cube of the Euclidean norm of the whitened vector $(a_i x_i,a_i y_i)$ is at most $\frac{4|a_i|^3}{\sqrt{1-\rho^2}}$.

**Proof.** First express the integral as an expectation under the finite correlated-pair distribution (`pmfExpectation_eq_integral`). For each sign pair, the cube of the whitened norm is bounded by one of two values: $(\sqrt{2}|a_i|/\sqrt{1+\rho})^3$ when the two signs agree, and $(\sqrt{2}|a_i|/\sqrt{1-\rho})^3$ when they differ (`regularThresholdPairSummand_whitening_norm_cube_le`). Averaging this pointwise bound preserves the inequality. The agreement and disagreement probabilities are respectively $(1+\rho)/2$ and $(1-\rho)/2$, so the resulting expectation is the corresponding weighted sum (`pmfExpectation_if_coordinate_signs_eq`). The elementary weighted scale estimate bounds that sum by $4|a_i|^3/\sqrt{1-\rho^2}$ (`weighted_whitening_scale_cube_le`), proving the claim.

**Key facts.** `FABL.pmfExpectation_eq_integral`, `FABL.regularThresholdPairSummand_whitening_norm_cube_le`, `FABL.pmfExpectation_if_coordinate_signs_eq`, `FABL.weighted_whitening_scale_cube_le`.
