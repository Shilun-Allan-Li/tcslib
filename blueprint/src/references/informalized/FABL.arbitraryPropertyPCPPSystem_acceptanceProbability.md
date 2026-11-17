<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.arbitraryPropertyPCPPSystem_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability of the Mixed Verifier

**Claim.** The verifier that chooses uniformly between the property-testing and coordinate-consistency verifiers has acceptance probability equal to the arithmetic mean of their acceptance probabilities on the given input and proof.

**Proof.** Apply the acceptance formula for a uniformly mixed verifier ($\texttt{uniformMixtureFunctionTester_acceptanceProbability}$): its acceptance probability is the average over the two component verifiers. For a uniform choice from a two-element set, this average is the sum of the two acceptance probabilities divided by $2$. Substituting the two component verifiers and the concatenated input and proof gives the claimed identity.

**Key facts.** `FABL.uniformMixtureFunctionTester_acceptanceProbability`.
