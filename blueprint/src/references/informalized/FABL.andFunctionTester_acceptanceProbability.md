<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.andFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjunction Tester Acceptance Probability

**Claim.** The tester that runs two nonadaptive testers with independent seeds and accepts exactly when both accept has acceptance probability equal to the product of their individual acceptance probabilities.

**Proof.** The combined seed is sampled by first drawing a seed for $T$ and then, independently, a seed for $U$. The expectation over this bind distribution can be written as an iterated expectation (`pmfExpectation_bind`); mapping the second seed into the seed pair is handled by the expectation-under-map identity (`pmfExpectation_map`). The combined tester accepts precisely when both component acceptance indicators equal $1$. Their product is exactly the indicator that both accept, as a direct check of the two Boolean cases shows. For each fixed seed of $T$, the factor depending only on that seed can be pulled out of the expectation over $U$ (`pmfExpectation_const_mul`). The remaining constant factor can then be pulled out of the expectation over $T$ (`pmfExpectation_mul_const`). The result is the product of the two separate acceptance expectations, which is the claimed identity.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_mul_const`.
