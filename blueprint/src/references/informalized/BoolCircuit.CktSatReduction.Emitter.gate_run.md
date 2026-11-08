<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine.lean :: BoolCircuit.CktSatReduction.Emitter.gate_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runtime of gate emission

**Claim.** Starting the machine in gate-emission state at program counter zero with counters encoded by $(z,a,b)$, it reaches the specified read state with counters $(z+1,0,0)$ and the emitted gate bits appended, within $200(M+1)$ steps when all counters are at most $M$.

**Proof.** Apply the instruction-suffix execution result to the entire gate program, starting at counter zero. It reaches an emission state whose counter is past the program and whose output includes the execution of the program; the program-length bound is at most 56. One further transition enters the first clearing state, preserving the emitted output. The first clear walk erases tape 1 and resets its head, and a second transition starts clearing tape 2. The second clear walk erases tape 2 and resets its head. A final transition increments tape 0 by one and enters the read state. The unary-tape update facts identify these changes with the counter vector $(z+1,0,0)$, while the other tape contents are empty. The input head stays fixed throughout. The total time is the suffix run plus these clearing and transition costs; using $v(1),v(2)\le M$ and the program-length bound gives at most $200(M+1)$.

**Key facts.** `BoolCircuit.CktSatReduction.Emitter.em_loop`, `BoolCircuit.CktSatReduction.Emitter.length_prog_le`, `BoolCircuit.CktSatReduction.Emitter.step_some`, `BoolCircuit.CktSatReduction.Emitter.apply_act`, `Turing.moveInputPos_zero`, `BoolCircuit.CktSatReduction.Emitter.clear_walk`, `BoolCircuit.CktSatReduction.Emitter.tapesOf_update`, `BoolCircuit.CktSatReduction.Emitter.headsOf_update_zero`, `Turing.UnaryTape.ones_zero`, `Turing.UnaryTape.update_ones_succ`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
