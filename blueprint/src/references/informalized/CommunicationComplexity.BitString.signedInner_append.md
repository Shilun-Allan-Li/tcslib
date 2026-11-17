<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BitString.lean :: CommunicationComplexity.BitString.signedInner_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity under concatenation

**Claim.** The signed inner product of two concatenated bit strings is the sum of the signed inner products of their respective blocks.

**Proof.** Expand the signed inner product as a sum over the $m+n$ coordinates and split that sum into its first $m$ coordinates and its last $n$ coordinates, using the decomposition of a sum over $	ext{Fin }(m+n)$. On the first block, concatenation evaluates to $x_1$ and $y_1$, so the summand is exactly the one defining their signed inner product. On the second block, reindexing its coordinates by $	ext{Fin }n$ makes the summand exactly the one defining the signed inner product of $x_2$ and $y_2$. Adding these two block sums gives the claimed identity.
