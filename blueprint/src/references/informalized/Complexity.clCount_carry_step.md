<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCount_carry_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Carry Transition

**Claim.** From carry control with tape holding $u$ followed by $v$ and work head at $|u|$, one transition leaves the input head and output unchanged. If the head of $v$ is true, the machine writes false there, advances the work head, and remains in carry control; otherwise it writes true there, moves the work head back by one with natural subtraction, and enters rewind control.

**Proof.** The transition function in carry control reads the symbol under the work head. The tape-reading fact identifies this symbol with the head of $v$ (`clCountTape_read`). If it is true, the machine's carry action writes false at cell $|u|$, advances the work head by one, and retains carry control. If it is not true—including when $v$ is empty—the action writes true and enters rewind control while moving the head back one cell. The tape update is precisely the replacement of the suffix head by the chosen bit (`clCountTape_write`). In both branches the action leaves the input head fixed, by the zero-movement property (`Turing.moveInputPos_zero`), and emits no output. These componentwise facts give the stated resulting configurations.

**Key facts.** `Complexity.clCountTape_read`, `Complexity.clCountTape_write`, `Turing.moveInputPos_zero`.
