<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_productCoordinateLaplacian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient of the coordinate Laplacian

**Claim.** The Fourier coefficient of the coordinate Laplacian at $a$ is the coefficient of $f$ at $a$ if $a_i$ is nonconstant, and zero if $a_i$ is the constant index.

**Proof.** The coordinate Laplacian is the difference between $f$ and its coordinate projection. Fourier coefficients take differences to differences (FABL.FiniteFourierBasis.fourierCoeff_sub). The coefficient of the projection equals that of $f$ when $a_i$ is the constant index, and is zero otherwise (FABL.FiniteFourierBasis.fourierCoeff_coordinateProjection). If $a_i$ is constant, subtraction cancels the two coefficients; if it is nonconstant, the projection contributes zero, leaving the coefficient of $f$.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_sub`, `FABL.FiniteFourierBasis.fourierCoeff_coordinateProjection`.
