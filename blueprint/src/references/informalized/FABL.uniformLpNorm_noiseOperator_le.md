<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.uniformLpNorm_noiseOperator_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise operator contraction

**Claim.** For $0\le\rho\le1$ and $p\ge1$, the uniform $L^p$ norm of the noise-operator image of a function on $\{−1,1\}^n$ is at most the uniform $L^p$ norm of the function.

**Proof.** Apply the anisotropic product noise contraction theorem to the Boolean cube, choosing the same parameter $\rho$ at every coordinate. Its hypotheses hold because each coordinate parameter lies in $[0,1]$, and $p\ge1$. The constant-parameter identity for the anisotropic operator identifies this image with the spectral product noise operator; the spectral operator agrees with the product noise operator. On the uniform sign distribution, the product noise operator is exactly the noise operator in the claim, and the product $L^p$ norm is the uniform $L^p$ norm. Translating both sides by these identifications gives the asserted contraction.

**Key facts.** `FABL.FiniteFourierBasis.productLpNorm_anisotropicProductNoiseOperator_le`, `FABL.anisotropicProductNoiseOperator_const`, `FABL.spectralProductNoiseOperator_eq_productNoiseOperator`, `FABL.productNoiseOperator_uniformSign_eq_noiseOperator`, `FABL.productLpNorm_uniformSign_eq_uniformLpNorm`.
