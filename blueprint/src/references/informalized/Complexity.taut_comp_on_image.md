<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_comp_on_image -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition on the Computation Image

**Claim.** If $M$ computes $f$ within time $T_1$ and $U$, on input $f(x)$, computes $g(x)$ within time $T_2(|x|)$, then a finite machine computes $g$ within time $2T_1(n)+T_2(n)+2$.

**Proof.** Use the buffered composition machine built from $M$ and $U$. For an input $x$, the first-machine computation reaches a configuration from which the buffered machine can simulate $U$ on $f(x)$; the startup theorem for buffered composition (`Turing.FinTM.bufferedComp_start`) bounds this setup time $a$ by $T_1(|x|)+|f(x)|+2$. Since a machine can emit at most one output symbol per step, $|f(x)|\le T_1(|x|)$ (`Turing.MultiTapeTM.output_length_le`), so $a\le 2T_1(|x|)+2$. Starting from that buffered configuration, the second machine's run for $T_2(|x|)$ steps is simulated faithfully (`Turing.FinTM.bufferedSecondCfg_run`). The assumed time bound for $U$ says that this run has halted and produced $g(x)$ (`Turing.FinTM.computesInTime_iff`); the buffered simulation therefore also halts with that output. The run-addition law (`Turing.MultiTapeTM.runFrom_add`) combines the setup and simulation into a run of length $a+T_2(|x|)$. The time bound follows from the estimate on $a$, and the machine remains correct if allowed to run for a larger time by monotonicity of the time-computation predicate (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.bufferedComp_start`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
