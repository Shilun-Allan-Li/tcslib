<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Meyer.lean :: Complexity.Meyer.mem_iff_final -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership from the Final Configuration

**Claim.** For a machine deciding $L$ within the stated time bound, a Boolean word $x$ belongs to $L$ exactly when, after the specified number of steps, the machine is halted and its output register contains the single bit $1$.

**Proof.** The bound `width_ok` shows that the specified time is at least the time within which $M$ decides $L$. By the monotonicity of computation in time (`Turing.FinTM.ComputesInTime.mono`), the machine therefore computes the same output and is halted at the specified time. The characterization of computation in time (`Turing.FinTM.computesInTime_iff`) gives these two facts about the final configuration directly. Its state is `none`, and its output is the one-bit list containing the indicator of whether $x\in L$. If $x\in L$, that indicator is true, so the output register is `OutReg.one true`; if $x\notin L$, the indicator is false, so the register is `OutReg.one false`. Thus the halted state together with `OutReg.one true` is equivalent to $x\in L$.

**Key facts.** `Complexity.Meyer.width_ok`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.computesInTime_iff`.
