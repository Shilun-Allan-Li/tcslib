<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.off_add_rlen_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Offset and Segment Length Bound

**Claim.** For a finite list of segments and any valid index $j$, the offset before segment $j$ plus its rendered length is at most the length of the virtual word.

**Proof.** Induct on the segment list, generalizing the index. The empty list has no valid index. For a singleton list, validity forces $j=0$; its offset is zero, and the virtual word is exactly the rendered segment, whose length is its rendered length. For a list with at least two segments, if $j=0$, the same length calculation shows that the segment length is at most the whole virtual-word length. If $j$ is a successor, apply the induction hypothesis to the tail at the preceding index. The offset definition adds the first segment's rendered length and the two-bit separator length, while the virtual word's length adds those same quantities to the tail's virtual-word length. The index lookup in the tail agrees with the original lookup (`seg_cons_succ`), and rendered length equals `rlen` (`length_render`); combining these identities gives the bound.

**Key facts.** `Complexity.LogProg.seg_cons_succ`, `Complexity.LogProg.length_render`.
