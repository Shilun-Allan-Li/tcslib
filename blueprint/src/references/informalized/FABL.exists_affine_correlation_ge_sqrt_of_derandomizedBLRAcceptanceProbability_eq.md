<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.exists_affine_correlation_ge_sqrt_of_derandomizedBLRAcceptanceProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Correlation from Acceptance

**Claim.** If the derandomized BLR acceptance probability is $\tfrac12+\tfrac12\theta$ and the density has bias at most $\varepsilon$, some affine function has sign correlation at least $\sqrt{\theta^2-\varepsilon}$ with the sign encoding of $f$, and relative Hamming distance at most one half minus half this quantity.

**Proof.** Let $F$ be the real sign encoding and $C=F*F$. Sign-valuedness of $F$ (`isSignValued_realSignEncodedFunction`) lets the acceptance-to-convolution estimate `sq_le_expectation_convolution_sq_of_derandomizedBLRAcceptanceProbability_eq` give $\theta^2\le\mathbb E_\phi[C^2]$. The bias estimate `ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le` bounds the difference from the uniform mean of $C^2$ by $\varepsilon$ times the squared Fourier one-norm. That one-norm equals $1$ for this self-convolution (`fourierOneNorm_binaryFunctionOnSignCube_convolution_self_eq_one`), and `mean_sq_binaryFunctionOnSignCube` identifies the uniform mean with $\mathbb E[C^2]$. Therefore $\theta^2-\varepsilon\le\mathbb E[C^2]$, which equals the fourth Fourier moment of $F$ (`vectorFourierFourthMoment_eq_expect_convolution_mul_self`). Some squared Fourier coefficient is at least this fourth moment (`exists_vectorFourierFourthMoment_le_sq_vectorFourierCoeff`). Applying `exists_affine_correlation_ge_sqrt_of_exists_sq_vectorFourierCoeff` gives the asserted affine correlation and distance bounds.

**Key facts.** `FABL.isSignValued_realSignEncodedFunction`, `FABL.sq_le_expectation_convolution_sq_of_derandomizedBLRAcceptanceProbability_eq`, `FABL.fourierOneNorm_binaryFunctionOnSignCube_convolution_self_eq_one`, `FABL.ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le`, `FABL.mean_sq_binaryFunctionOnSignCube`, `FABL.vectorFourierFourthMoment_eq_expect_convolution_mul_self`, `FABL.exists_vectorFourierFourthMoment_le_sq_vectorFourierCoeff`, `FABL.exists_affine_correlation_ge_sqrt_of_exists_sq_vectorFourierCoeff`.
