<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.runFrom_output_eq_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output stability after halting

**Claim.** If the machine has halted by time $\tau$, then for every $t\geq\tau$ the outputs at times $t$ and $\tau$ are equal.

**Proof.** Write $t=\tau+(t-\tau)$, which is valid because $\tau\leq t$. The run decomposition law (`runFrom_add`) identifies the configuration at time $t$ with the result of running another $t-\tau$ steps from the configuration at time $\tau$. That configuration is halted by hypothesis, so the run-from-halt result (`runFrom_of_halt`) says it remains unchanged. Thus the configurations, and in particular their outputs, agree.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
