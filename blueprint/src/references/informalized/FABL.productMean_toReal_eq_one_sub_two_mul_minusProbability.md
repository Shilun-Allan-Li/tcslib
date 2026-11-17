<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.productMean_toReal_eq_one_sub_two_mul_minusProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Mean from Minus Probability

**Claim.** For a sign-valued random variable, its mean is one minus twice the probability that it equals $-1$.

**Proof.** A sign is either $1$ or $-1$. Pointwise, its value equals $1-2$ times the indicator that it is $-1$. Taking expectations and using additivity, the expectation of a constant, and homogeneity of expectation (`pmfExpectation_add_fun`, `pmfExpectation_const`, and `pmfExpectation_smul_fun`) gives one minus twice the expectation of that indicator, which is precisely the stated probability.

**Key facts.** `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_smul_fun`.
