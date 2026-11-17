<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferTape_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Buffer Tape

**Claim.** The buffer tape storing the empty word contains no symbol at any integer cell.

**Proof.** Fix an integer cell $z$. If $0\le z$, the buffer tape reads the entry of the empty word at the natural-number index corresponding to $z$, which is absent. If $z<0$, the definition returns no symbol directly. Thus every cell contains no symbol, so the buffer tape is the constant function with value `none`.
