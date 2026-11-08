<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine.lean :: BoolCircuit.CktSatReduction.Emitter.move_ip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward input-head movement

**Claim.** If $i<|w|$, then a rightward move from the input-head position corresponding to $i$ gives the position corresponding to $i+1$.

**Proof.** The position corresponding to $i$ has value $i+1$. Since $i<|w|$, this value is not the right boundary position $|w|+1$. Thus the right-movement rule applies without boundary clamping: it increases the position by one. The result has value $i+2$, which is exactly the position corresponding to $i+1$.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`.
