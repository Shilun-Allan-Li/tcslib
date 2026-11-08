<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.alwaysRejectF₂CubeFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Always-Reject Acceptance Probability

**Claim.** For any function on the binary cube, the tester that always rejects has acceptance probability zero.

**Proof.** For every seed, the tester's acceptance predicate is false. Its acceptance-probability expectation is therefore the constant zero function. The constant-expectation identity (`pmfExpectation_const`) says that the expectation of a constant is that constant, so the acceptance probability is zero.

**Key facts.** `FABL.pmfExpectation_const`.
