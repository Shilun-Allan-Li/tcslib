<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HomogeneousMoments.lean :: FABL.sq_le_fourierSparsity_mul_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Bound by Fourier Sparsity

**Claim.** At every point of the sign cube, the square of $f(x)$ is at most the Fourier sparsity of $f$ times the uniform average of $f(y)^2$.

**Proof.** Expand $f(x)$ as the sum of its Fourier coefficients over the Fourier support (`fourier_expansion_support`). The finite-sum Cauchy–Schwarz inequality bounds the square of this sum by the product of the sum of squared coefficients and the sum of squared monomials over that support. Every monomial has square one (`monomial_sq`), so the latter sum is the size of the support, namely the Fourier sparsity. Parseval's identity identifies the sum of squared coefficients on the support with the uniform average of $f(y)^2$ (`sum_sq_fourierCoeff_support`). Multiplying these two factors gives the claim.

**Key facts.** `FABL.fourier_expansion_support`, `FABL.monomial_sq`, `FABL.sum_sq_fourierCoeff_support`.
