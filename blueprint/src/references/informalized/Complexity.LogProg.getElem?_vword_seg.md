<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.getElem?_vword_seg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries Within a Rendered Segment

**Claim.** For a valid segment index $i$, entries within the rendered segment at offset $k$ in the virtual word agree with the entries of that segment’s rendering, provided $k$ is within its rendered length.

**Proof.** Induct on the list of segments, with the index $i$ generalized. For a singleton list, validity forces $i=0$, and the virtual word is just that segment’s rendering, so the assertion follows directly. For a list with at least two segments, first consider $i=0$. The virtual word begins with the rendering of the first segment; the bound on $k$ places the requested index within this initial block, so indexing the concatenation returns the same entry as indexing that rendering. If $i$ is a successor, the segment at that index is the corresponding segment of the tail (`seg_cons_succ`), and its offset is the length of the first rendering plus the two separator bits plus its offset in the tail. The requested index is therefore past the initial rendering-and-separator block. Removing that block reduces the claim to the induction hypothesis for the tail. The zero-index segment identification used above is `seg_cons_zero`.

**Key facts.** `Complexity.LogProg.seg_cons_zero`, `Complexity.LogProg.seg_cons_succ`.
