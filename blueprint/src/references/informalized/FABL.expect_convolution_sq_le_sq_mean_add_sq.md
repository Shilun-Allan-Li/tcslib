<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.expect_convolution_sq_le_sq_mean_add_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convolution second-moment bound

**Claim.** If the nonzero Fourier coefficients of the density are bounded in absolute value by $\varepsilon$ and $F$ is sign-valued, then the average square of their convolution is at most $(\mathbb E F)^2+\varepsilon^2$.

**Proof.** By the convolution Parseval identity, the average square is the sum over frequencies of $\widehat\varphi(\gamma)^2\widehat F(\gamma)^2$ (`expect_convolution_sq_eq_sum_sq_vectorFourierCoeff`). Separate the zero frequency from all nonzero ones. At zero, the density coefficient is its mean, which is $1$ by the density normalization, and the coefficient of $F$ is its mean (`ProbabilityDensity.expect_eq_one`, `vectorFourierCoeff_zero_eq_mean`). Thus this term is $(\mathbb E F)^2$.

For every nonzero frequency, the bias assumption gives $|\widehat\varphi(\gamma)|\leq\varepsilon$. In particular $\varepsilon\geq0$, and squaring yields $\widehat\varphi(\gamma)^2\leq\varepsilon^2$. Each remaining summand is therefore at most $\varepsilon^2\widehat F(\gamma)^2$. Summing over the nonzero frequencies and enlarging to all frequencies can only increase the sum, since the added terms are nonnegative. Parseval applied to $F$ and the fact that $F$ is sign-valued give $\sum_\gamma\widehat F(\gamma)^2=1$ (`sum_sq_vectorFourierCoeff_eq_one`). Hence the nonzero-frequency contribution is at most $\varepsilon^2$, proving the bound.

**Key facts.** `FABL.expect_convolution_sq_eq_sum_sq_vectorFourierCoeff`, `FABL.ProbabilityDensity.expect_eq_one`, `FABL.vectorFourierCoeff_zero_eq_mean`, `FABL.sum_sq_vectorFourierCoeff_eq_one`.
