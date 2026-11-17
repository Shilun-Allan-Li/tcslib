<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.abs_vectorFourierCoeff_innerProductModTwoSupportDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of the Support Density

**Claim.** For $m>0$ and nonzero $\gamma\in\mathbb F_2^{2m}$, the absolute value of the Fourier coefficient of the density uniform on the support of the inner-product-mod-two function is $(2^{-m})/(1-2^{-m})$.

**Proof.** The support is nonempty, so its uniform probability $p$ is positive: at a point in the support, the indicator in the defining expectation is $1$. The density at each point is therefore $p^{-1}$ times the Boolean real embedding of the inner-product-mod-two bit function (`innerProductModTwoSupportDensity_apply`). Multiplying a function by a constant multiplies its Fourier coefficient by that constant (`vectorFourierCoeff_const_mul`); taking absolute values contributes the positive factor $p^{-1}$. The nonzero-index coefficient of the Boolean real embedding has magnitude $2^{-m}/2$ (`abs_vectorFourierCoeff_booleanRealEmbedding_innerProductModTwoBit_of_ne_zero`), while the support probability is $p=(1-2^{-m})/2$ (`uniformProbability_innerProductModTwoOneSet`). Substituting these expressions and canceling the factor $1/2$ gives $2^{-m}/(1-2^{-m})$. Positivity of $p$ ensures the denominator is nonzero.

**Key facts.** `FABL.innerProductModTwoOneSet_nonempty`, `FABL.innerProductModTwoSupportDensity_apply`, `FABL.vectorFourierCoeff_const_mul`, `FABL.abs_vectorFourierCoeff_booleanRealEmbedding_innerProductModTwoBit_of_ne_zero`, `FABL.uniformProbability_innerProductModTwoOneSet`.

**Caveat.** The formal theorem proves the stated coefficient magnitude. It does not formalize the additional claim in the prose payload that this is the smallest possible bias parameter.
