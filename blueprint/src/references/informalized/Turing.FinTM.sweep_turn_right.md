<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweep_turn_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Turn from Backward to Forward Scan

**Claim.** Applying the specified right-moving action to a backward-facing zipper configuration yields the forward-facing zipper configuration with frontier increased by one, the written symbol at the head of the new left stack, the old left stack as the new right stack, and unchanged input position and output.

**Proof.** The action leaves the input position fixed (`moveInputPos_zero`) and emits no output. It writes $b$ at the backward-facing frontier. The tape-write identity (`sweepTape_write`) describes the updated tape by inserting $b$ at the head of the current right stack. Reflecting the tape orientation with `sweepTape_turn`, and using $z+1-1=z$, identifies it as a forward-facing zipper with frontier $z+1$, left stack beginning with $b$ followed by the former right-stack tail, and right stack equal to the former left stack. These are the asserted configuration components.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.sweepTape_write`, `Turing.FinTM.sweepTape_turn`.
