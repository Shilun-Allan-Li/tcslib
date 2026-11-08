<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedMinusProbabilityPolynomial_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial probability identity

**Claim.** For $p\in[0,1]$, the biased minus-probability polynomial equals the probability that $f$ takes the value $-1$ under the corresponding product distribution.

**Proof.** The biased expectation polynomial at the bias corresponding to $p$ equals the product-distribution expectation of the real-valued function associated with $f$ (biasedExpectationPolynomial_biasMean). For any probability law on the sign cube, that expectation is $1$ minus twice the probability that $f=-1$ (productMean_toReal_eq_one_sub_two_mul_minusProbability), because $f$ takes only the values $1$ and $-1$. Substituting this identity into the polynomial’s definition, which divides one minus the expectation by two, yields the stated probability.

**Key facts.** `FABL.biasedExpectationPolynomial_biasMean`, `FABL.productMean_toReal_eq_one_sub_two_mul_minusProbability`.
