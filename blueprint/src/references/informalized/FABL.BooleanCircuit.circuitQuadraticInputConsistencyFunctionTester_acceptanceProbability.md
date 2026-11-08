<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticInputConsistencyFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Consistency Acceptance Probability

**Claim.** For positive input length, the input consistency tester’s acceptance probability on an input and proof equals the average over input coordinates of the probability that the local correction of the sign-valued function encoded by the inner proof agrees with the sign encoding of the corresponding input bit.

**Proof.** Rewrite the input consistency tester as the padded version of its three-query tester; padding preserves acceptance probability (`padThreeQueryFunctionTester_acceptanceProbability`). The three-query tester uses the uniform distribution on seeds, so its acceptance probability is the expectation of its acceptance indicator (`pmfExpectation_uniformPMF_eq_expect`). A seed consists of an input coordinate and a uniformly chosen cube point. The transcript definitions identify the queried proof values, and the acceptance condition becomes exactly that the local correction at the chosen point equals the sign encoding of the input bit at that coordinate. Finally, the expectation over the product seed space is the average over coordinates of the uniform probability over cube points, which is the stated affine-coordinate correction probability. The transcript identity (`NonadaptiveFunctionTester.transcript_apply`) supplies the values read at each query.

**Key facts.** `FABL.padThreeQueryFunctionTester_acceptanceProbability`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.NonadaptiveFunctionTester.transcript_apply`.
