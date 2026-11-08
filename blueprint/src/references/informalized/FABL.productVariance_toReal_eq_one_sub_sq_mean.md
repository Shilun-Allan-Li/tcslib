<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.productVariance_toReal_eq_one_sub_sq_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Sign-Valued Function

**Claim.** For a sign-valued random variable represented by a function on a finite probability space, its variance is one minus the square of its mean.

**Proof.** Let $m$ be the mean of the sign-valued function. Each value is either $-1$ or $1$, so its square is identically $1$. Expand the centered square pointwise as $f^2-2mf+m^2$. Expectation is additive (FABL.pmfExpectation_add_fun), scales linearly under multiplication of a function by a constant (FABL.pmfExpectation_smul_fun), and sends a constant function to that constant (FABL.pmfExpectation_const). Consequently the expectation of the expansion is $1-2m^2+m^2=1-m^2$, as claimed.

**Key facts.** `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_smul_fun`, `FABL.pmfExpectation_const`.
