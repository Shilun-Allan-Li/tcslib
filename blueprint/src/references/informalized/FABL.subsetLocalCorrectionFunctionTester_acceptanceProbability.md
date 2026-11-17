<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.subsetLocalCorrectionFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability of the Local Correction Tester

**Claim.** The tester’s acceptance probability equals the uniform probability that the local correction of the sign-encoded function, at the point corresponding to the subset indicator, is $-1$.

**Proof.** The tester samples a uniform binary vector $y$ and queries the sign-encoded function at $y$ and at $x+y$, where $x$ is the binary vector corresponding to the subset indicator. Its acceptance rule accepts exactly when the product of the two answers is $-1$. Thus, after expressing the tester’s acceptance probability as an expectation over its uniform seed, the integrand is the indicator that this product equals $-1$. By the uniform-PMF expectation identity (`pmfExpectation_uniformPMF_eq_expect`), this expectation is the uniform expectation over $y$. The product is precisely the local correction at $x$ and $y$, so the expectation is the stated uniform probability.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
