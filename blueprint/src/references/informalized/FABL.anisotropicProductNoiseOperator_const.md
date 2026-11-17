<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.anisotropicProductNoiseOperator_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant-Parameter Noise Agreement

**Claim.** When every coordinate has the same noise parameter $\rho$, the anisotropic product noise operator agrees with the spectral product noise operator.

**Proof.** By injectivity of the Fourier coefficient map ($\texttt{FiniteFourierBasis.fourierCoeff_injective}$), it suffices to show that the two outputs have the same coefficient at each multi-index $a$. The coefficient of the anisotropic output is the coefficient of $f$ multiplied by $\prod_i(1\text{ if }a_i\text{ is the distinguished index, and }\rho\text{ otherwise})$ ($\texttt{FiniteFourierBasis.fourierCoeff_anisotropicProductNoiseOperator}$). This product has one factor of $\rho$ for each coordinate where $a_i$ is not the distinguished index, and factors of $1$ elsewhere. It therefore equals $\rho^{\mathrm{order}(a)}$, where the order counts those coordinates. For the spectral output, its defining expansion has coefficient $\rho^{\mathrm{order}(b)}\widehat f(b)$ at each basis product indexed by $b$. Uniqueness of the Fourier expansion ($\texttt{FiniteFourierBasis.fourier_expansion_unique}$) identifies its coefficient at $a$ as $\rho^{\mathrm{order}(a)}\widehat f(a)$. The two coefficients agree for every $a$, proving equality of the functions.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_injective`, `FABL.FiniteFourierBasis.fourierCoeff_anisotropicProductNoiseOperator`, `FABL.FiniteFourierBasis.fourier_expansion_unique`.
