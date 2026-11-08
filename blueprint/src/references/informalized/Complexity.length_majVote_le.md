<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean :: Complexity.length_majVote_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for an Encoded Vote

**Claim.** For either bit $b$ and any bit string $a$, the specified encoded pair has length at most $|a|+4$.

**Proof.** Let $p$ and $q$ be the lengths of the total first and second projections of $a$. The projection bound gives $2p+q\le |a|$ (`Complexity.length_pair_components_le`). If $b=1$, the encoding doubles the first projection after prepending one bit, inserts the two-bit separator, and appends the second projection. Its length is $2(p+1)+2+q=2p+q+4\le |a|+4$. If $b=0$, the first projection is unchanged and one bit is prepended to the second, so the length is $2p+2+(q+1)=2p+q+3\le |a|+4$.

**Key facts.** `Complexity.length_pair_components_le`, `Turing.length_pairEncode`.
