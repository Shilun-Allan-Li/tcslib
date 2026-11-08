<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Silent Scan of a Suffix

**Claim.** If $x=\mathrm{pre}++r$, then starting in scanner state $q$ at position $|\mathrm{pre}|+1$ with output $o$, the dual transducer scans $r$ in exactly $|r|$ steps, reaches scanner state $r$ folded from $q$ at position $|x|+1$, preserves $o$, and avoids the anchor state throughout the segment.

**Proof.** Induct on the suffix $r$. If it is empty, the initial and final configurations coincide, and a zero-length segment has no earlier times to check (`Complexity.tautDual_segment_zero`). For a nonempty suffix $b::r$, the first input symbol at position $|\mathrm{pre}|+1$ is $b$ (`Complexity.tautDual_read`). The scanner transition therefore advances one position, changes its syntax state to the transition of $q$ on $b$, and emits no output; the action-on-configurations identity gives this resulting configuration (`Complexity.tautDual_action`). The head advances by one because the current position is not the right boundary (`Turing.moveInputPos_pos_of_ne_right`). Since this first configuration is a scanning state, not the anchor, it forms an anchor-free one-step segment (`Complexity.tautDual_segment_one`). Apply the induction hypothesis to the remaining suffix from the new prefix and scanner state, then concatenate the one-step segment and the remaining scan using the segment-composition lemma (`Complexity.tautDual_segment_add`). The concatenated length is $1+|r|$, and the successive scanner transitions are exactly the fold over $b::r$.

**Key facts.** `Complexity.tautDual_segment_zero`, `Complexity.tautDual_read`, `Complexity.tautDual_action`, `Turing.moveInputPos_pos_of_ne_right`, `Complexity.tautDual_segment_one`, `Complexity.tautDual_segment_add`.
