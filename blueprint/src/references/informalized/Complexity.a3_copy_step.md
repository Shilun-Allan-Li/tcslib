<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_copy_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Copy Transition

**Claim.** When $i<|x|$, one wrapper step from the copy-phase configuration at input position $i+1$, with tape zero holding the length-$i$ prefix and its head at $i$, produces the copy-phase configuration at input position $i+2$, with the length-$(i+1)$ prefix and its head at $i+1$; the other tapes remain blank with heads at zero, and the output remains empty.

**Proof.** In the given configuration the input head reads $x_i$, by the fact that a configuration whose input position is $i+1$ reads the input symbol at index $i$ (`inputSymbolInner`). The wrapper’s phase-$0$ transition on a present input symbol moves the input head one position to the right, writes that symbol on tape zero at its current head position, and moves that tape head one position right; it leaves every other tape and the output unchanged. Since $i<|x|$, the input head is not at the right boundary, so its positive move reaches position $i+2$ (`moveInputPos_pos_of_ne_right`). Tape zero previously held $x$ through index $i-1$ and its head was at $i$, so writing $x_i$ there produces the prefix of length $i+1$. The identity expressing a list prefix extended by its next element, together with the description of how the buffer tape changes when an element is appended (`bufferTape_append`), verifies the tape contents at every integer position. Thus all configuration fields agree with the claimed next copy-phase configuration.

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
