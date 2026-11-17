<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferTape_nat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffer tape at natural cells

**Claim.** At natural cell $i$, the buffer tape for $w$ contains exactly the optional $i$-th symbol of $w$.

**Proof.** A natural number is nonnegative, so the buffer-tape definition selects the list lookup at its natural index. That lookup is precisely the optional $i$-th symbol of $w$.
