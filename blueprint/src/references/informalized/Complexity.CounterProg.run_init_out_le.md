<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.run_init_out_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output-Length Bound from the Initial State

**Claim.** Starting from the initial state at any label, after $t$ steps the output has length at most $t(t+1)$.

**Proof.** Induct on $t$. At $t=0$, the initial output is empty, so the bound holds. For the induction step, decompose the run of $t+1$ steps into a run of $t$ steps followed by one step, using the run decomposition law (`Complexity.CounterProg.run_add`). After the first $t$ steps, every register is at most $t$: the register growth bound (`Complexity.CounterProg.run_regs_le`) gives this because every register initially equals zero. The one-step output bound (`Complexity.CounterProg.step_out_le`) therefore says that the next step increases output length by at most $t+1$. Combining this with the induction hypothesis gives $t(t+1)+(t+1)=(t+1)(t+2)$, as required.

**Key facts.** `Complexity.CounterProg.run_add`, `Complexity.CounterProg.run_regs_le`, `Complexity.CounterProg.step_out_le`.
