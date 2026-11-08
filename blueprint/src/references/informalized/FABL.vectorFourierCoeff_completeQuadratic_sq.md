<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.vectorFourierCoeff_completeQuadratic_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Coefficient of the Complete Quadratic

**Claim.** For even $n$ and every $\gamma\in\mathbb F_2^n$, the square of the vector Fourier coefficient of the sign encoding of the complete quadratic bit at $\gamma$ is $2^{-n}$.

**Proof.** Apply the Fourier convolution identity to the complete quadratic and itself at the support of $\gamma$ (`FABL.binaryFourierCoeff_convolution`). For even $n$, their convolution is the indicator of the zero vector (`FABL.convolution_completeQuadratic_self`). The Fourier coefficient of that singleton indicator is $2^{-n}$ (`FABL.binaryFourierCoeff_singletonIndicator`). The convolution identity therefore says that the product of the two identical coefficients is $2^{-n}$; by the definition of the vector coefficient, this product is its square.

**Key facts.** `FABL.binaryFourierCoeff_convolution`, `FABL.convolution_completeQuadratic_self`, `FABL.binaryFourierCoeff_singletonIndicator`.
