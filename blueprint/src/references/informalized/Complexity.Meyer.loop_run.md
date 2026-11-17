<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.loop_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded simulation of a machine run

**Claim.** If the counter word has value $v$, the simulated machine can be brought from the specified decode configuration to the write-decode configuration corresponding to the original machine's $v$-step run, in at most $(v+1)(2|w|+3)$ simulator steps, with suitable auxiliary tape contents and head positions.

**Proof.** Use strong induction on $v$, with the counter word and starting configuration allowed to vary. The proof maintains the virtual boundary tag and carries the output register and auxiliary output tape through the simulation.

1. If $v=0$, a zero-valued counter word consists entirely of zeros (`ctrVal_zero_eq`). The decode sweep (`dec_sweep`) traverses this word and reaches the position just beyond it; there the auxiliary tape is blank, so the machine switches from decode to write-decode (`dec_under`). This takes $|w|+1$ steps, within the stated bound. The original machine has run for zero steps, and the boundary tag is unchanged.

2. If $v>0$, write the counter word as $0^j1$ followed by a remaining suffix, using the positive-counter decomposition (`ctrVal_pos_decomp`). The decode sweep moves the simulator head to the first $1$. That cell contains true (`bufferTape_at`), so the machine fires one simulated transition (`dec_fire`), writes false there, and moves its auxiliary head back one position. The updated tape is the counter word with that $1$ cleared (`bufferTape_update_mid`); the borrow identity (`ctrVal_borrow`) shows its value is $v-1$. Its length is still $|w|$, so the induction hypothesis applies to the next original configuration.

3. If the original machine halts on that transition, the simulator is already in the write-decode state. The run remains there thereafter (`runFrom_of_halt`), and the new tag satisfies the boundary condition. The sweep and firing costs fit within the claimed bound.

4. If the original machine continues in state $q'$, the simulator first returns its auxiliary head to the start of the counter (`ret_sweep`), then runs the induction hypothesis on the updated counter and the next original configuration. The run-composition identities (`runFrom_succ_eq_step`, `runFrom_succ_eq_step'`, and `runFrom_add`) concatenate these phases. The return and firing cost is bounded by $2|w|+3$, while the recursive phase is bounded by $v(2|w|+3)$; together they give $(v+1)(2|w|+3)$. The induction hypothesis supplies the final auxiliary tape and head position, and the simulated machine's run agrees with the original run after $v$ steps.

**Key facts.** `Complexity.TimeHierarchy.ctrVal_zero_eq`, `Complexity.Meyer.dec_sweep`, `Complexity.Meyer.dec_under`, `Complexity.TimeHierarchy.ctrVal_pos_decomp`, `Complexity.Meyer.bufferTape_at`, `Complexity.Meyer.dec_fire`, `Complexity.TimeHierarchy.bufferTape_update_mid`, `Complexity.TimeHierarchy.ctrVal_borrow`, `Turing.MultiTapeTM.runFrom_of_halt`, `Complexity.Meyer.ret_sweep`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`.
