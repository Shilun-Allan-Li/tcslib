<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPGaps.lean :: FABL.PCPPSystem.acceptanceProbability_le_optimumAcceptance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Below the Maximum

**Claim.** For every input word and proof word, the verifier's acceptance probability is at most the maximum acceptance probability over all such pairs.

**Proof.** The optimum is defined by choosing a pair of input and proof words that maximizes the verifier's acceptance probability over the finite space of all such pairs. The maximum property says that the value at any particular pair is no greater than this chosen maximum. Applying it to the given input and proof yields the inequality.
