<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.NonadaptiveFunctionTester.acceptanceProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability upper bound

**Claim.** The probability that the tester accepts the transcript produced by querying the given function is at most $1$.

**Proof.** For each seed, the indicator of acceptance is either $0$ or $1$, and hence is at most the constant function $1$. Monotonicity of expectation under the seed distribution gives that the acceptance probability is at most the expectation of this constant function. A probability distribution assigns expectation $1$ to the constant function $1$, proving the bound.

**Key facts.** `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const_one`.
