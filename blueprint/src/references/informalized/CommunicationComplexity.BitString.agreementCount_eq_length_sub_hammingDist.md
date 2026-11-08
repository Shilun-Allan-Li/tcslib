<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BitString.lean :: CommunicationComplexity.BitString.agreementCount_eq_length_sub_hammingDist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Count as a Complement

**Claim.** For two $n$-bit strings $x$ and $y$, their agreement count, regarded as an integer, equals $n$ minus their Hamming distance.

**Proof.** The preceding counting identity says that the agreement count plus the Hamming distance equals $n$ as an equality of natural numbers. Regard that identity as an equality of integers; subtracting the Hamming distance from both sides gives the claimed formula.

**Key facts.** `CommunicationComplexity.BitString.agreementCount_add_hammingDist_eq_length`.
