<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.pal_test_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entering the Test Phase

**Claim.** One step from the stated configuration in state $1$ yields the specified configuration in state $2$, advancing the input head to $1$ and moving the work head to $|x|-1$, while preserving the copied tape and empty output.

**Proof.** At input position $0$, the input head reads no symbol, so the transition rule for state $1$ applies to a blank input. Unfolding the step and transition shows that the successor state is $2$, the input head moves one position to the right, the work head moves from $|x|$ to $|x|-1$, no work-tape symbol is written, and no output is appended. The input-head movement formula gives position $1$ from position $0$ (the current position is not the right boundary). Thus every field of the resulting configuration agrees with the claimed one.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`.
