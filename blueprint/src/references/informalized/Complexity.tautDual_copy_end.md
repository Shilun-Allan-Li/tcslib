<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_copy_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# End of the Copying Pass

**Claim.** At the end of the input, a copying configuration at position $|x|+1$ takes one step to the rewind state with its flag true at position $|x|$, leaving the output unchanged; the anchor state is not visited during this segment.

**Proof.** At position $|x|+1$, the input head sees no symbol, since this is the right endmarker position. In copying state, the end-of-input transition moves left into rewind state with flag true and emits no bit. The action rule therefore leaves the output unchanged, and the left move takes the head from $|x|+1$ to $|x|$. The starting copying state is not the anchor state, so the one-step segment has no earlier anchor visit.

**Key facts.** `Complexity.tautDual_read`, `Complexity.tautDual_action`, `Turing.moveInputPos_neg_of_ne_left`, `Complexity.tautDual_segment_one`.
