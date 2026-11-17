<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_fourierComponentAtSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient of a fixed support component

**Claim.** The Fourier coefficient at $a$ of the component supported on $J$ equals the coefficient of $f$ at $a$ when the nonconstant-coordinate support of $a$ is $J$, and is zero otherwise.

**Proof.** Expand the component as a finite sum over multi-indices whose nonconstant-coordinate support is $J$. By linearity of Fourier coefficients, its coefficient at $a$ is the sum of the coefficients of those terms. The coefficient of a scalar multiple of a product basis function is that scalar times the coefficient of the basis function; orthonormality of the product basis makes this zero for every index other than $a$, and leaves the coefficient of $f$ at $a$ when the index is $a$. If the support of $a$ is $J$, this is the sole surviving summand. If it is not, the index $a$ is absent from the sum, so every term vanishes.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_sum`, `FABL.FiniteFourierBasis.fourierCoeff_ite`, `FABL.FiniteFourierBasis.fourierCoeff_smul`, `FABL.FiniteFourierBasis.fourierCoeff_zero`, `FABL.FiniteFourierBasis.fourierCoeff_productFunction`.
