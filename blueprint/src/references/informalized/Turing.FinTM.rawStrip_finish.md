<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.rawStrip_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of rewind and replay

**Claim.** Starting in state $2$ with $a$ on the work tape, the head at $|a|-1$, and empty output, after $2(|a|+1)$ steps the machine is halted and its output is exactly $a$.

**Proof.** Split the time as $(|a|+1)+(|a|+1)$. The rewind result (`rawStrip_rewind`), applied with $j=|a|$, shows that the first $|a|+1$ steps place the machine in state $3$, with the head at coordinate $0$, while preserving the stored word and empty output. The replay result (`rawStrip_replay`) then applies for $j=|a|$: the next $|a|$ steps emit the first $|a|$ bits of $a$, which is all of $a$, and leave the head at coordinate $|a|$. One further step halts in state `none` without changing the output. The run decomposition facts (`runFrom_add` and `runFrom_succ_eq_step'`) identify these phases with the stated total time.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.rawStrip_rewind`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.rawStrip_replay`.
