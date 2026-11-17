<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.pal_test_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching Test-Phase Transition

**Claim.** If the bit of $x.reverse$ at position $i$ agrees with the bit of $x$ at position $i$, one test-phase step advances the input head to $i+2$ and moves the work head one position left, preserving the copied tape and empty output.

**Proof.** The input head at position $i+1$ reads $x[i]$ by the input-symbol rule for an interior position (Turing.inputSymbolInner). By the work-tape reading result (Complexity.pal_test_read), the work head reads $x.reverse[i]$; the assumed equality makes these symbols agree. The test-state transition for matching symbols therefore keeps the machine in state $2$, moves the input head right, moves the work head left, and writes neither to the work tape nor to the output. Since $i+1$ is not the right boundary, the input-head movement rule (Turing.moveInputPos_pos_of_ne_right) sends it to $i+2$. The two head positions and all unchanged configuration fields are exactly those claimed.

**Key facts.** `Complexity.pal_test_read`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`.
