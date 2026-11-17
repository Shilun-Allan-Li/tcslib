<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPSystem_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability of the Combined Verifier

**Claim.** For a circuit with positive input length, the combined verifier’s acceptance probability is the average of the inner-function tester’s and input-consistency tester’s acceptance probabilities on the word formed from the input and proof.

**Proof.** The combined verifier is a uniform mixture of the two testers. The uniform-mixture acceptance identity says its acceptance probability is the expectation of the two component acceptance probabilities over a uniformly chosen tester (FABL.uniformMixtureFunctionTester_acceptanceProbability). A uniform choice from two possibilities has expectation equal to their sum divided by two. Applying this to the word formed from the input and proof gives the stated formula.

**Key facts.** `FABL.uniformMixtureFunctionTester_acceptanceProbability`.
