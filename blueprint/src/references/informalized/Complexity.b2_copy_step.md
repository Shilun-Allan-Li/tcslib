<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_copy_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One input-copying step

**Claim.** For $i<|x|$, one host step from copy state at position $i+1$, with the first $i$ symbols of $x$ on the assembly buffer, reaches copy state at position $i+2$ with the first $i+1$ symbols on the buffer.

**Proof.** Because $i<|x|$, the input head at position $i+1$ reads $x_i$ (`inputSymbolInner`). In copy state $0$, the host writes that bit into the assembly buffer and moves the input head right; since the position is not the right boundary, the right-move formula (`moveInputPos_pos_of_ne_right`) gives position $i+2$. The buffer update appends the newly read bit to the prefix already stored: `bufferTape_append` identifies this append with writing the bit at the old buffer-head position, and the list-prefix identities identify the resulting contents with the first $i+1$ symbols of $x$. The assembly-buffer head advances by one, while all other tapes, heads, and the output remain unchanged. These componentwise facts give the asserted configuration.

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
