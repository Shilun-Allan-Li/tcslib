<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_pairValid_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair validation time bound

**Claim.** For every finite bit string $x$, the pair-validation machine halts within $|x|+1$ steps and outputs the one-symbol word recording whether the aligned pair parser is defined on $x$.

**Proof.** The run lemma for pair validation (`f2_pairValid_run`) applied with the whole input as the remaining suffix and the empty prefix gives a time $t\le |x|+1$ at which the machine has halted and produced the desired indicator. The machine's initial configuration is exactly the scanning configuration at position zero with empty output: this follows by comparing their state, input position, and output, which determine a zero-work-tape configuration (`Cfg.ext_zero_tapes`). The characterization of computation in time (`computesInTime_iff`) therefore turns the two run conclusions into computation of the required output at time $t$. Since $t\le |x|+1$, monotonicity of computation time (`ComputesInTime.mono`) gives the stated bound.

**Key facts.** `Turing.FinTM.f2_pairValid_run`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
