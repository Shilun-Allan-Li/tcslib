<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Program.lean :: Complexity.LogProg.seg_argSegs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Argument Segment Description

**Claim.** For each valid index $i$ in a list of Boolean words, its argument segment is the pair consisting of the word at position $i$ and a flag that is true exactly when another word follows.

**Proof.** Proceed by induction on the list of words, allowing the index to vary. The empty list has no valid index. For a singleton list, validity forces the index to be zero; its only segment is the word paired with `false`, and no index remains after it. For a list with at least two words, index zero selects the head word, paired with `true`, because another word follows. At a positive index, segment lookup drops the list head (`seg_cons_succ`), reducing the claim to the induction hypothesis on the tail. The tail's length is one less than the original length, so the index bound transfers; the description of whether another word follows agrees with the original list's corresponding bound.
