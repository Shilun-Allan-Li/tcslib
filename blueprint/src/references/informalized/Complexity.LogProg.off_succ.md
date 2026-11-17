<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.off_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Segment Offsets

**Claim.** If $i+1$ is a valid index in the segment list, its offset is the offset at $i$ plus the rendered length of segment $i$ and the two-bit separator length.

**Proof.** Induct on the segment list, generalizing $i$. The empty list is impossible under the index bound. For a nonempty list, the case $i=0$ follows directly from the offset definition. When $i$ is a successor, unfold the offset on the list and use the induction hypothesis on the tail. The tail lookup at the preceding index is the original list's lookup at $i+1$ (`seg_cons_succ`). The resulting sums agree after reassociating their terms.

**Key facts.** `Complexity.LogProg.seg_cons_succ`.
