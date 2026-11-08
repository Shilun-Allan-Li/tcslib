<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferTape_inputSymbol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffer tape reads the input symbol

**Claim.** At cell $p-1$, the buffer tape for $w$ contains exactly the optional symbol read by the input head of $c$, where $p$ is the shifted input-head position.

**Proof.** If the shifted head position is zero, then $p-1$ is negative, so the buffer tape is blank there; the input symbol is also absent at the left boundary. Otherwise the head position is positive, and its integer cell $p-1$ is the natural index $c.\mathrm{inputPos}.\mathrm{val}-1$. At a natural cell $i$, the buffer tape equals the optional $i$-th list entry (`Turing.FinTM.bufferTape_nat`). The input-symbol-at-position fact (`Turing.FinTM.inputSymbol_at`) says that when the shifted head position is $i+1$, the input symbol is precisely that optional entry. Applying it with this index gives the claimed equality.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.inputSymbol_at`.
