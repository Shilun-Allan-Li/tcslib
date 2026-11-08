<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean :: CommunicationComplexity.exists_true_of_ne_zeroInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A nonzero input has a true coordinate

**Claim.** If an $n$-bit Boolean input differs from the all-zero input, then some coordinate of it is true.

**Proof.** Suppose, to the contrary, that no coordinate is true. At each coordinate the value is Boolean, so it must be false. The input therefore agrees with the all-zero input at every coordinate, and hence is equal to it, contradicting the hypothesis. Thus some coordinate is true.
