<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.affineSubspacePCPPSystem_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability of the affine subspace system

**Claim.** The system's acceptance probability is the average of the acceptance probabilities of its affine-subspace proof tester and affine-consistency tester on the combined input and proof word.

**Proof.** The verifier is the uniform mixture of the two testers, so its acceptance probability is the expectation of their acceptance probabilities over a uniformly chosen index (uniform-mixture acceptance formula, `FABL.uniformMixtureFunctionTester_acceptanceProbability`). The index set has two elements, and this expectation is their sum divided by $2$. The PCPP system evaluates that verifier on the combined input and proof word, yielding the claimed formula.

**Key facts.** `FABL.uniformMixtureFunctionTester_acceptanceProbability`.
