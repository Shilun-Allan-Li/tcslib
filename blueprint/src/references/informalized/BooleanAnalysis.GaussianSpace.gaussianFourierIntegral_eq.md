<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.gaussianFourierIntegral_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Fourier Integral Formula

**Claim.** The Fourier transform paired with the Gaussian Fourier pairing equals the Gaussian integral of $H$ against the character with phase $a\sum_j t_jx_j$.

**Proof.** Rewrite the vector Fourier integral using the standard formula that expresses it as an integral of the exponential of the pairing phase times the function (`Real.vector_fourierIntegral_eq_integral_exp_smul`). The phase of the Gaussian Fourier pairing is $a\sum_j t_jx_j$ (`gaussianFourierPairing_phase`). Substituting this identity into the exponential gives exactly the stated integrand; the remaining scalar and complex notation agree by the definitions of the pairing and scalar multiplication.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianFourierPairing_phase`.
