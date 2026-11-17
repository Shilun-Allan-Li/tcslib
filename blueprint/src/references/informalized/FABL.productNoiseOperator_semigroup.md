<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productNoiseOperator_semigroup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Noise Semigroup

**Claim.** Applying product noise at parameters $\rho$ and $\sigma$ in succession is the same as applying it once at parameter $\rho\sigma$.

**Proof.** Use injectivity of the Fourier-coefficient representation (FABL.FiniteFourierBasis.fourierCoeff_injective), so it suffices to compare the coefficients at each multi-index. Noise at parameter $\sigma$ multiplies the coefficient by $\sigma^{\mathrm{order}(a)}$, and subsequent noise at parameter $\rho$ multiplies it by $\rho^{\mathrm{order}(a)}$ (FABL.FiniteFourierBasis.fourierCoeff_productNoiseOperator). Their product is $(\rho\sigma)^{\mathrm{order}(a)}$, which is exactly the multiplier for noise at parameter $\rho\sigma$. The product lies in $[0,1]$ by the given bounds, so this parameter is admissible. Hence all coefficients agree, proving the identity.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_injective`, `FABL.FiniteFourierBasis.fourierCoeff_productNoiseOperator`.
