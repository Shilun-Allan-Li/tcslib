<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.vpos_right_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Boundary of the Final Segment

**Claim.** If $s$ indexes the final segment, the virtual position immediately to its right is one more than the length of the concatenated virtual word.

**Proof.** The hypothesis $s+1=|\text{segs}|$ ensures the list is nonempty and that its final index is $|\text{segs}|-1$. The length formula for a nonempty virtual word (`length_vword`) expresses its length as the offset of the final segment plus that segment’s rendered length. By definition, the right-boundary position at index $s$ is the same offset plus one plus that rendered length. Substituting the length formula and using $s=|\text{segs}|-1$ gives the desired equality.

**Key facts.** `Complexity.LogProg.length_vword`.
