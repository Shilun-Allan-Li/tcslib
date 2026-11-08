<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_copy_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Input-Copy Step

**Claim.** For every Boolean word $x$ and $i<|x|$, one step from the specified copy-phase configuration reaches the configuration with the first $i+1$ bits copied, both heads advanced by one, and output still empty.

**Proof.** Because $i<|x|$, the input-head position $i+1$ points to the bit $x[i]$ (inputSymbolInner). In the copy state, the machine writes that bit on the work tape and advances the input and work heads. The input head therefore moves from $i+1$ to $i+2$ (moveInputPos_pos_of_ne_right); the bound on $i$ ensures this is not the right endmarker. Appending $x[i]$ to the previously copied prefix gives the first $i+1$ bits, and the buffer-tape update at the old end position is exactly the tape representing that appended word (bufferTape_append). The transition emits no output, so the output remains empty.

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
