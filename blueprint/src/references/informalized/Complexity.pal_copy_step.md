<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.pal_copy_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single Copy-Phase Transition

**Claim.** For $t<|x|$, one step from the copy-phase configuration at input position $t+1$, with the first $t$ bits copied and work head at $t$, reaches the corresponding configuration with the first $t+1$ bits copied, input head at $t+2$, and work head at $t+1$; the output remains empty.

**Proof.** At input position $t+1$ the machine reads $x_t$ (`inputSymbolInner`). Its state-$0$ transition writes that bit at the current work-head cell $t$, moves the input head one position right, and moves the work head one cell right; the input-head movement gives position $t+2$ by `moveInputPos_pos_of_ne_right`. The tape after the write is precisely the tape for the first $t+1$ bits by `palTape_write`. The transition preserves state $0$ and emits no output, giving all components of the claimed configuration.

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Complexity.palTape_write`.
