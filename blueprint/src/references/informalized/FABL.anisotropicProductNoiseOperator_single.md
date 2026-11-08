<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.anisotropicProductNoiseOperator_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-Coordinate Noise Agreement

**Claim.** When the anisotropic parameter is $\rho$ at coordinate $i$ and $1$ elsewhere, the anisotropic product noise operator equals the operator that applies noise only at coordinate $i$.

**Proof.** Use injectivity of the Fourier coefficient map ($\texttt{FiniteFourierBasis.fourierCoeff_injective}$) and compare coefficients at an arbitrary multi-index $a$. The anisotropic operator multiplies the coefficient of $f$ by the product over coordinates of $1$ when $a_j$ is the distinguished index and the parameter at $j$ otherwise ($\texttt{FiniteFourierBasis.fourierCoeff_anisotropicProductNoiseOperator}$). Since the parameter is $1$ away from $i$, all factors away from $i$ are $1$; the remaining factor is $1$ if $a_i$ is distinguished and $\rho$ otherwise. This is exactly the coefficient multiplier for the single-coordinate operator ($\texttt{FiniteFourierBasis.fourierCoeff_productSingleCoordinateNoiseOperator}$). Thus every Fourier coefficient agrees, so the operators agree.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_injective`, `FABL.FiniteFourierBasis.fourierCoeff_anisotropicProductNoiseOperator`, `FABL.FiniteFourierBasis.fourierCoeff_productSingleCoordinateNoiseOperator`.
