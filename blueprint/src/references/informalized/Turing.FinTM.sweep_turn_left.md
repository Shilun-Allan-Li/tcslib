<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweep_turn_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Turn from Forward to Backward Scan

**Claim.** Applying the specified left-moving action to a forward-facing zipper configuration produces the backward-facing configuration with frontier decreased by one, the written symbol at the head of the new right stack, the old left stack as the new right stack, and the stated input and output updates.

**Proof.** The action leaves the input position subject only to its prescribed movement, changes the state to $q'$, writes $b$ at the current frontier, and appends the optional emitted symbol to the output. The tape-write identity (`sweepTape_write`) replaces the head entry of the forward right stack by $b$. The change-of-orientation identity (`sweepTape_turn`) then expresses this same tape as a backward-facing zipper: its frontier is $z-1$, its right stack begins with $b$ and continues with the former right-stack tail, and its left stack is the old left stack. The output append and input-position update are exactly those specified by the action.

**Key facts.** `Turing.FinTM.sweepTape_write`, `Turing.FinTM.sweepTape_turn`.
