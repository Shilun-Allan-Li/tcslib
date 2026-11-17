<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.getD_flatten_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries in flattened blocks

**Claim.** If every block in a finite list of lists has length $w$, then position $wj+t$ of their concatenation, for a valid block index $j$ and $t<w$, contains the entry at position $t$ of block $j$.

**Proof.** The decomposition lemma for flattened blocks (`take_drop_flatten`) identifies the $j$th block with the length-$w$ segment beginning at position $wj$ in the concatenation: dropping the first $wj$ entries and taking the next $w$ gives precisely that block. Looking at position $t<w$ in this segment therefore gives the entry at position $t$ of the block. The hypotheses ensure both positions are in range, so the shared default value does not affect either lookup.

**Key facts.** `Complexity.Codec.take_drop_flatten`.
