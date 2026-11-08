<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.abs_integral_sub_taylor_polynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Taylor Polynomial Error

**Claim.** The difference between the expectation of $\psi(a+bX)$ and the expectation of its degree-$m$ Taylor polynomial at $a$ is bounded by the stated derivative and absolute-moment expression.

**Proof.** First ensure the terms can be integrated. Finite $(m+1)$st moment gives integrability of each power $(bX)^j$ for $j\le m+1$ (`integrable_mul_pow_of_memLp`), so the Taylor polynomial is integrable. The composed test function is integrable by the corresponding composition result (`integrable_test_of_memLp`). Subtract their integrals and bound the absolute value by the integral of the pointwise absolute Taylor remainder. At each $\omega$, the scalar Taylor estimate (`abs_sub_taylor_le`) bounds that remainder by $\frac{C}{(m+1)!}|bX(\omega)|^{m+1}$. Integrating and factoring out $|b|^{m+1}$ yields the claimed bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.integrable_mul_pow_of_memLp`, `BooleanAnalysis.GaussianSpace.integrable_test_of_memLp`, `BooleanAnalysis.GaussianSpace.abs_sub_taylor_le`.
