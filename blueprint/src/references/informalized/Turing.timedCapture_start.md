<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCapture_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reaching Interpreter Entry

**Claim.** If the original machine is halted after $T$ steps from its initial configuration, then by time $T+1$ the capture machine reaches the interpreter-entry configuration associated with that halted configuration.

**Proof.** Among the times at which the original run is halted, choose the least one, $t$. Such a time exists because the run is halted at $T$, and minimality gives $t\leq T$. The configuration at time $T$ equals the one at time $t$: write $T=t+d$ and use that a halted configuration remains fixed under every further run step (`MultiTapeTM.runFrom_add` and `MultiTapeTM.runFrom_of_halt`). By the initialization identity (`timedCapture_init`) and the lockstep result, the capture machine after $t$ steps is the embedding of the original time-$t$ configuration; the lockstep hypothesis holds because minimality ensures the run has not halted at any earlier time. One further capture step transfers this embedded halted configuration to interpreter entry (`timedCapture_transfer`). Consequently the capture machine reaches the interpreter-entry configuration at time $t+1$, and $t+1\leq T+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.timedCapture_init`, `Turing.timedCapture_run`, `Turing.timedCapture_transfer`.
