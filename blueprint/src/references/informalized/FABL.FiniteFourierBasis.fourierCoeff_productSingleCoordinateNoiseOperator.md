<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_productSingleCoordinateNoiseOperator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient under single-coordinate noise

**Claim.** Applying the single-coordinate noise operator multiplies the Fourier coefficient at $a$ by $1$ when $a_i$ is the constant index, and by $\rho$ otherwise.

**Proof.** The operator is the sum of the coordinate projection and $\rho$ times the coordinate Laplacian. Linearity makes its coefficient the sum of the projection coefficient and $\rho$ times the Laplacian coefficient. When $a_i$ is constant, the projection contributes the coefficient of $f$ and the Laplacian contributes zero. When $a_i$ is nonconstant, the projection contributes zero and the Laplacian contributes the coefficient of $f$. These two cases give the stated multiplier.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_add`, `FABL.FiniteFourierBasis.fourierCoeff_smul`, `FABL.FiniteFourierBasis.fourierCoeff_coordinateProjection`, `FABL.FiniteFourierBasis.fourierCoeff_productCoordinateLaplacian`.
