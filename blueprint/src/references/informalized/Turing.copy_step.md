<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.copy_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying One Input Symbol

**Claim.** For each $i<|x|$, one step from the copy configuration for the prefix of length $i$ yields the copy configuration for the prefix of length $i+1$.

**Proof.** At input position $i+1$, the input-symbol-at-position fact gives the current symbol as $x[i]$ (Turing.inputSymbolInner). The copy-state transition therefore writes this symbol on the first work tape, advances that tape's head and the input head by one, and leaves the other tapes and output unchanged. The prefix identity $x.take(i+1)=x.take(i)++[x[i]]$ shows that the new tape contents are precisely the buffer for the longer prefix: appending one symbol to a word-buffer updates its value at the old word length and leaves its other cells unchanged (Turing.FinTM.bufferTape_append). Since the old prefix has length $i$, this update occurs at the old head position. The input head does not encounter the right boundary because $i<|x|$, so its positive move is exactly one position forward (Turing.moveInputPos_pos_of_ne_right). The work-head position and all unchanged components then agree with the next copy configuration.

**Key facts.** `Turing.inputSymbolInner`, `Turing.FinTM.bufferTape_append`, `Turing.moveInputPos_pos_of_ne_right`.
