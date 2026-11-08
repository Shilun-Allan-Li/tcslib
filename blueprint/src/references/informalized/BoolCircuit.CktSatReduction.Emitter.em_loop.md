<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine.lean :: BoolCircuit.CktSatReduction.Emitter.em_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of an instruction suffix

**Claim.** From an emission state whose program suffix is the instruction list $r$, the machine reaches an emission state whose program counter is past the program, preserves its input position and work tapes, and appends the execution of $r$ to the output within $|r|(2M+3)$ steps.

**Proof.** Induct on $r$. If $r$ is empty, the program counter already points beyond the program: the equality between the dropped program and the empty list gives this, and zero steps suffice. For the induction step, write $r$ as an instruction followed by a suffix. The same equality identifies the instruction at the current counter and shows that the counter increased by one points to the remaining suffix; the program-length bound ensures the current counter is in range. If the instruction outputs a bit, one transition appends that bit and advances to the next emission counter. Apply the induction hypothesis to the suffix with that updated output. If the instruction prints tape $t$, one transition enters the printing routine. The print walk emits $v(t)$ copies of true and reaches the return routine; the back walk restores the head to its original position and returns to emission at the next counter. Thus this instruction contributes the execution of the print instruction, and the induction hypothesis handles the suffix. The time bound follows by adding the one-step output cost, or the $2(v(t)+1)+1$ steps for printing and returning, to the suffix bound; since $v(t)\le M$, each instruction costs at most $2M+3$.

**Key facts.** `BoolCircuit.CktSatReduction.Emitter.length_prog_le`, `BoolCircuit.CktSatReduction.Emitter.step_some`, `BoolCircuit.CktSatReduction.Emitter.apply_ctl`, `Turing.moveInputPos_zero`, `BoolCircuit.CktSatReduction.Emitter.apply_act`, `BoolCircuit.CktSatReduction.Emitter.print_walk`, `BoolCircuit.CktSatReduction.Emitter.back_walk`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
