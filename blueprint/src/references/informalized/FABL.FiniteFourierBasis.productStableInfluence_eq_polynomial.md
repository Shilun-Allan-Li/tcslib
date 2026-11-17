<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.productStableInfluence_eq_polynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence Polynomial Formula

**Claim.** For $0<\rho\le 1$, the stable influence at coordinate $i$ equals the sum of squared Fourier coefficients over multi-indices nonconstant at $i$, weighted by $\rho^{|S|-1}$, where $|S|$ is the size of the multi-index support.

**Proof.** Expand the noise stability of the coordinate Laplacian in its Fourier representation (`productNoiseStability_eq_sum`), and multiply by $\rho^{-1}$ as in the definition of stable influence. The coordinate Laplacian coefficient formula (`fourierCoeff_productCoordinateLaplacian`) makes every term vanish when the multi-index is constant at $i$; otherwise its coefficient is the original Fourier coefficient. For a surviving index, its support size $k$ is positive (`multiIndexOrder_pos_of_ne`), so write $k=m+1$. The stability weight then has exponent $k$, and division by $\rho$ changes it to $\rho^{k-1}$; this is valid because $\rho>0$. Summing the surviving terms gives the stated stable-influence polynomial.

**Key facts.** `FABL.FiniteFourierBasis.productNoiseStability_eq_sum`, `FABL.FiniteFourierBasis.fourierCoeff_productCoordinateLaplacian`, `FABL.multiIndexOrder_pos_of_ne`.

**Caveat.** The supplied informal statement describes a derivative identity for total stable influence. The formal theorem and proof establish the coordinate stable-influence polynomial identity given in the claim.
