<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.coordinateConsistencyFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Consistency Tester Acceptance Probability

**Claim.** The tester’s acceptance probability equals the uniform average over coordinates of the probability that the local correction agrees with the input bit.

**Proof.** Expand acceptance probability as the expectation of the indicator that the tester accepts, and use the uniform-law expectation formula (\texttt{pmfExpectation\_uniformPMF\_eq\_expect}). Unfolding the tester’s transcript and acceptance rule shows that acceptance is exactly the event that the product of the two proof signs, at $y$ and at its translate by the coordinate truth table, equals the sign encoding of the input bit. The tester samples a coordinate and a vector independently and uniformly, so the finite expectation over their product space is the uniform average over coordinates of the expectation over $y$. For each fixed coordinate, this latter expectation is precisely the uniform probability that the local correction equals the sign encoding of the corresponding bit. This yields the stated average.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
