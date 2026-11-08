<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.NonadaptiveFunctionTester.acceptanceProbability_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative acceptance probability

**Claim.** The probability that the tester accepts the transcript produced by querying the given function is nonnegative.

**Proof.** The constant zero function has expectation zero. At each seed, the acceptance indicator is either zero or one, so it is at least zero. Monotonicity of expectation therefore bounds the expectation of this indicator below by zero; this expectation is the acceptance probability.

**Key facts.** `FABL.pmfExpectation_const`, `FABL.pmfExpectation_mono`.
