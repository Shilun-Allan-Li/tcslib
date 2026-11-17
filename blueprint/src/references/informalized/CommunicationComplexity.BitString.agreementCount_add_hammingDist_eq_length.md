<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BitString.lean :: CommunicationComplexity.BitString.agreementCount_add_hammingDist_eq_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement and Hamming Distance Partition the Coordinates

**Claim.** For two $n$-bit strings, the number of coordinates on which they agree plus their Hamming distance equals $n$.

**Proof.** A coordinate either satisfies $x_i=y_i$ or fails that equality, and these two conditions partition all coordinates. The cardinalities of the corresponding subsets therefore sum to the cardinality of the full coordinate set, which is $n$. By definition, the first cardinality is the agreement count and the second is the Hamming distance.
