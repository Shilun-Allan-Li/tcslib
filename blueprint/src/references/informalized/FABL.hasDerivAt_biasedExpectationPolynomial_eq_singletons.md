<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.hasDerivAt_biasedExpectationPolynomial_eq_singletons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative from singleton Fourier coefficients

**Claim.** For $p\in(0,1)$, the derivative of the biased expectation polynomial at $1-2p$ is $\sigma(p)^{-1}\sum_{i=1}^n\widehat f_p(\{i\})$.

**Proof.** First use the derivative formula for the biased expectation polynomial (`FABL.hasDerivAt_biasedExpectationPolynomial`) at $\mu=1-2p$. The sum of its degree-weighted Fourier terms is also the sum, over coordinates $i$, of the biased product expectations of the discrete derivatives (`FABL.sum_productMean_biasedSignPMF_discreteDerivative`). For each coordinate, the singleton biased Fourier coefficient equals $\sigma(p)$ times that discrete-derivative expectation (`FABL.biasedFourierCoeff_singleton_eq_sigma_mul_expect_discreteDerivative`). Summing these identities and dividing by the nonzero quantity $\sigma(p)$—positive for $p\in(0,1)$ by `FABL.biasSigma_pos`—rewrites the derivative as the claimed singleton-coefficient sum.

**Key facts.** `FABL.hasDerivAt_biasedExpectationPolynomial`, `FABL.sum_productMean_biasedSignPMF_discreteDerivative`, `FABL.biasedFourierCoeff_singleton_eq_sigma_mul_expect_discreteDerivative`, `FABL.biasSigma_pos`.
