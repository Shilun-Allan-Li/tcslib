<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachineTapes.lean :: BoolCircuit.CktSatReduction.Emitter.apply_act -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a selected-tape action

**Claim.** A selected-tape action updates the chosen work tape at its head position and moves that head by the prescribed amount, while leaving the other work tapes and heads unchanged; it also sets the successor state, moves the input head as prescribed, and appends the optional output bit.

**Proof.** Compare the configuration fields. The action sets the state to $q$ and moves the input head to the clamped position determined by $p$ and $im$. For each work tape, split into whether its index is the selected tape $t$. At $t$, the action’s write and movement are exactly $wr$ at $h_t$ and $m$, so the tape becomes the update of $T_t$ there and its head becomes $h_t+m$. At every other index the action specifies no write and zero movement, leaving that tape and head unchanged. The output field appends the optional bit to $O$. All fields thus agree with the claimed configuration.
