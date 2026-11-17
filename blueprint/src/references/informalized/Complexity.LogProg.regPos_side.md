<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Call.lean :: Complexity.LogProg.regPos_side -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register positions determine the side of a segment

**Claim.** Under the stated consistency and validity conditions, if argument register $a$ is at position $-1$, the side predicate is true; if it is at the end of its word, the side predicate is false.

**Proof.** Because the argument list has no repetitions, the index of its $a$th entry is $a$. The segment at index $a+1$ contains that register’s word (`seg_callSegs_succ`). Consider the three possibilities in the position rule. If this segment is already past, the register is at the word’s right boundary; the segment index is strictly before $s$, so the side predicate is false. If the segment is still ahead, the register is at $-1$; the index is strictly after $s$, so the predicate is true. If this is the current segment, then $s=a+1$. At a left boundary, consistency forces the direction to be false, making the predicate true; at a right boundary, consistency forces it true, making the predicate false. For an interior cell, validity bounds its position between the two boundaries, so it cannot equal either endpoint in a way that contradicts the claimed implications. These cases establish both statements.

**Key facts.** `Complexity.LogProg.seg_callSegs_succ`.
