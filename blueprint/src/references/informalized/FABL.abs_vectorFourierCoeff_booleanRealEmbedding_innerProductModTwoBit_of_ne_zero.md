<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.abs_vectorFourierCoeff_booleanRealEmbedding_innerProductModTwoBit_of_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient Magnitude

**Claim.** For nonzero $\gamma\in\mathbb F_2^{2m}$, the absolute value of the Fourier coefficient of the Boolean real embedding of the inner-product-mod-two bit function is $((2^m)^{-1})/2$.

**Proof.** The Boolean real embedding coefficient is a scalar multiple of the coefficient of the real inner-product-mod-two function: the preceding coefficient identity gives the factor $-1/2$. Taking absolute values turns this factor into $1/2$. The absolute value of the latter function's coefficient is $(2^m)^{-1}$ (`abs_vectorFourierCoeff_innerProductModTwo`). Multiplying these magnitudes gives $((2^m)^{-1})/2$.

**Key facts.** `FABL.vectorFourierCoeff_booleanRealEmbedding_innerProductModTwoBit_of_ne_zero`, `FABL.abs_vectorFourierCoeff_innerProductModTwo`.
