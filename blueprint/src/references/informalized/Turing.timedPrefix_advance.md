<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedPrefix_advance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advancing the Parser One Step

**Claim.** Under the stated transition hypothesis, the parser advances its input head from position $p+1$ to $p+2$, preserves its clock buffer, appends the emitted symbol to its output, and enters state $q'$.

**Proof.** The configuration’s input head is at position $p+1$, so it reads the input bit at index $p$. The input-symbol-at-position fact (`Turing.FinTM.inputSymbol_at`), together with the hypothesis about that bit, identifies this reading as $b$. The transition hypothesis therefore supplies a right move, no work-tape change, emission $e$, and successor state $q'$. Applying this action preserves the work tape and its head, appends the emitted symbol to the output, and changes the state to $q'$. Since $p$ is strictly before the end of the input, the right-move position formula (`Turing.moveInputPos_pos_of_ne_right`) gives the new input-head position $p+2$.

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Turing.moveInputPos_pos_of_ne_right`.
