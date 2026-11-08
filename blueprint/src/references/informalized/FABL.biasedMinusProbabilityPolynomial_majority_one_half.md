<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedMinusProbabilityPolynomial_majority_one_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd majority at unbiased bias

**Claim.** For every nonnegative integer $m$, the biased minus-probability polynomial of majority on $2m+1$ coordinates at $p=1/2$ equals $1/2$.

**Proof.** The polynomial equals the minus-output probability under the corresponding product law (biasedMinusProbabilityPolynomial_eq). At $p=1/2$, each coordinate has the uniform sign distribution (biasedSignPMF_one_half_eq_uniform). Under the resulting uniform product law, odd-coordinate majority has mean zero (productMean_uniform_majority_odd_eq_zero). The expectation of a sign-valued function is one minus twice its probability of taking value $-1$ (productMean_toReal_eq_one_sub_two_mul_minusProbability). A zero mean therefore makes that probability $1/2$, proving the claim.

**Key facts.** `FABL.biasedMinusProbabilityPolynomial_eq`, `FABL.biasedSignPMF_one_half_eq_uniform`, `FABL.productMean_uniform_majority_odd_eq_zero`, `FABL.productMean_toReal_eq_one_sub_two_mul_minusProbability`.
