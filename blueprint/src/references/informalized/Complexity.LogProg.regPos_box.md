<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Call.lean :: Complexity.LogProg.regPos_box -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register positions lie in their boxes

**Claim.** For a valid track position at a segment index $s$ below the argument-list length, every register’s call position lies in its register box: registers outside the argument list retain their initial positions, and each listed register has position between $-1$ and the length of its word.

**Proof.** Fix a register $r$. If it is not in the argument list, the call-position rule leaves its initial position unchanged, as required. If it is in the list, its index identifies its segment, and the segment at that index contains exactly its word (`seg_callSegs_succ`). The position rule puts it at the left boundary $-1$ if its segment is still ahead, at the right boundary if its segment has already passed, and otherwise at the current track position. The boundaries are within the interval from $-1$ to the word length. In the current-segment case, validity of the track position gives the same bounds (`trackPos_bounds`).

**Key facts.** `Complexity.LogProg.seg_callSegs_succ`, `Complexity.LogProg.trackPos_bounds`.
