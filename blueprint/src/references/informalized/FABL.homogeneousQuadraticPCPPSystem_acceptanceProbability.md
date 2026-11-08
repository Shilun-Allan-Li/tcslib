<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.homogeneousQuadraticPCPPSystem_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance of the Mixture Verifier

**Claim.** The verifier’s acceptance probability is the arithmetic mean of the acceptance probabilities of its quadratic-pair, system, and input-consistency component testers on the same input and proof.

**Proof.** The verifier is defined by uniformly mixing the three component testers. The acceptance probability of a uniform mixture is the expectation, over the selected component, of that component’s acceptance probability (\texttt{uniformMixtureFunctionTester\_acceptanceProbability}). Since the component index ranges over three equally likely choices, this expectation is their sum divided by $3$. The PCPP system’s acceptance probability is the verifier’s acceptance probability on the combined input-proof word, so the claimed identity follows.

**Key facts.** `FABL.uniformMixtureFunctionTester_acceptanceProbability`.
