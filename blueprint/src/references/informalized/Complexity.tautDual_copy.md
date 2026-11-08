<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Suffix

**Claim.** For a decomposition $x=pr$, starting in copying state $q$ at the position just after $p$ with output $o$, the transducer reads all of $r$ in exactly $|r|$ steps, reaches the copying state given by scanning $r$ from $q$ at the end of $x$, and appends the polarity-adjusted scan of $r$ to the output. No earlier configuration is the anchor state.

**Proof.** Induct on the suffix $r$. If it is empty, the initial and final configurations coincide, and the zero-step segment property gives the claim. For $r=b::r'$, the machine first reads $b$ at the position immediately after $p$. The read rule identifies this input bit; the copying transition moves right, changes the syntax state to the state obtained by processing $b$, and appends the bit adjusted according to the current polarity. This one-step segment does not visit the anchor state. Apply the induction hypothesis to $r'$, now starting after $p$ followed by $b$, with the updated scanner state and output. Concatenating the one-step segment with this suffix segment gives the required endpoint and total length, while preserving the no-anchor condition.

**Key facts.** `Complexity.tautDual_read`, `Complexity.tautDual_action`, `Turing.moveInputPos_pos_of_ne_right`, `Complexity.tautDual_segment_one`, `Complexity.tautDual_segment_add`, `Complexity.tautDual_segment_zero`.
