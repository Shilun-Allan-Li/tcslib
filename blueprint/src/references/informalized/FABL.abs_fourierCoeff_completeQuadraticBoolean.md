<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.abs_fourierCoeff_completeQuadraticBoolean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Boolean Fourier magnitude

**Claim.** For even dimension, every Fourier coefficient of the real-valued complete quadratic Boolean function has absolute value $2^{-n/2}$.

**Proof.** Choose the binary vector $\gamma$ whose support is the given coordinate set $S$, using the bijection between binary vectors and coordinate subsets. The support of this vector is exactly $S$. The absolute vector Fourier coefficient of the complete quadratic function at $\gamma$ is $2^{-n/2}$ by the established quadratic coefficient formula (`abs_vectorFourierCoeff_completeQuadratic`). The identity relating vector Fourier coefficients to Fourier coefficients on the sign cube (`vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`) converts this into the coefficient indexed by the support of $\gamma$. Finally, the real-valued complete quadratic Boolean function agrees with the sign-cube version of the binary complete quadratic function (`completeQuadraticBoolean_toReal`), giving the asserted result.

**Key facts.** `FABL.abs_vectorFourierCoeff_completeQuadratic`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`, `FABL.completeQuadraticBoolean_toReal`.
