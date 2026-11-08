<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.support_dist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hamming distance from support size

**Claim.** The Hamming distance between two words equals the number of coordinates at which they differ.

**Proof.** By definition, the support of the pair of words is the finite set of coordinates where their values differ. Hamming distance is defined as the cardinality of precisely that set, so the two quantities are equal by unfolding their definitions.
