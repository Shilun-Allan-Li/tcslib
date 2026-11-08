<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.step_regs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Growth in One Step

**Claim.** After one program step, the value of register $r$ is at most its previous value plus one.

**Proof.** If the state is halted, the register is unchanged. For an active state, all instructions except increment either preserve this register or decrement it (with zero staying zero). Increment changes the selected register by exactly one and leaves every other register unchanged. In every case its new value is at most its old value plus one.
