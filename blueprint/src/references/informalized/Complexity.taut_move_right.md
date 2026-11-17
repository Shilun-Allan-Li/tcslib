<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_move_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a silent rightward move

**Claim.** Applying the silent action that moves the input head right, moves the work head by $e$, and enters state $q'$ produces the stated next configuration.

**Proof.** Compare the five configuration components. The action sets the control state to $q'$. For the input head, the current encoded position is $i+1$; the hypothesis $i+1\le |x|$ ensures this position is not the right boundary, so a positive move advances it to $i+2$, the position encoding $i+1$ consumed bits. This is the right-move position formula (`Turing.moveInputPos_pos_of_ne_right`). The action makes no work-tape write, so the work word is unchanged; its work-head displacement adds $e$ to the current position $h$. It emits no output, so the output word remains $o$. These componentwise equalities give the claimed configuration.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`.
