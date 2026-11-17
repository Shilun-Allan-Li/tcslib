<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.eq_flatten_blocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flattening equal-length blocks

**Claim.** If a list has length $wm$, then it is the concatenation, in order, of the $m$ consecutive blocks of length $w$ obtained by dropping $wj$ entries and taking the next $w$ entries for each $j<m$.

**Proof.** Induct on the number $m$ of blocks. With no blocks, the length hypothesis forces the list to be empty, so the claim holds. For $m+1$ blocks, the first block is the first $w$ entries of $u$. The remainder after dropping those entries has length $wm$, by the original length equation. Apply the induction hypothesis to this remainder: it is the concatenation of its $m$ blocks. Dropping $wj$ entries from the remainder is the same as dropping $w(j+1)$ entries from the original list, so these are exactly the blocks indexed after the first one. Finally, the original list is its first $w$ entries followed by the remainder, giving the stated concatenation.
