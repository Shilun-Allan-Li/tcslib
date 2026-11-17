<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.iterate_zipStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of the zip step

**Claim.** For every bit string $w$ and natural number $i$, applying the zip step $i+1$ times to $w$ gives the pair encoding of the tails obtained by removing the first $i+1$ bits from the total first and total second projections of $w$.

**Proof.** We induct on $i$. When $i=0$, the statement is exactly the definition of one zip step. For the successor case, write the next iterate as one zip step applied to the previous iterate. By the induction hypothesis, that previous iterate encodes the two projections with their first $i+1$ bits removed. Decoding this pair recovers those projections; the zip step removes one further bit from each. These are precisely the tails after removing $i+2$ bits, proving the result.
