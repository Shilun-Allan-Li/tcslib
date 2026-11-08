<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BitString.lean :: CommunicationComplexity.BitString.signedInner_eq_length_sub_twice_hammingDist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed inner product and Hamming distance

**Claim.** For two bit strings of length $n$, their signed inner product is $n-2$ times their Hamming distance.

**Proof.** At each coordinate, the contribution is $+1$ when the bits agree and $-1$ when they differ. This contribution can be written as $1-2$ times the indicator of disagreement: it is $1$ for agreement and $-1$ for disagreement. Summing over all coordinates gives $n$ minus twice the sum of the disagreement indicators. That sum is the Hamming distance, since it counts exactly the coordinates where the strings differ. Therefore the signed inner product is $n-2d_H(x,y)$.
