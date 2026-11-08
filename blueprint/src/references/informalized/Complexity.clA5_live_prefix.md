<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_live_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Live Prefixes of a Run

**Claim.** If the run from $c$ is live at time $t$, then it is live at every time $u\le t$.

**Proof.** Suppose instead that the configuration at time $u\le t$ is halted. The run composition law (`runFrom_add`) expresses the configuration at time $t$ as the result of continuing from time $u$. A halted configuration is unchanged by further steps (`runFrom_of_halt`), so the configurations at times $u$ and $t$ would be equal. That would make the time-$t$ configuration halted, contrary to the hypothesis.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
