<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.clockStageCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Correspondence Through the Clock Phase

**Claim.** If the masked machine is nonhalting at every time before $\tau$, then for each $t\le\tau$ the schedule machine after $t+1$ steps is the clock-stage configuration corresponding to the masked machine after $t$ steps.

**Proof.** Induct on $t$. At $t=0$, the claim is the initialization correspondence `clockStageCfg_init`. For the successor case, write the masked machine's configuration at time $t$ as having state $q$; this is possible because $t<\tau$ and the assumed nonhalting condition applies. By the induction hypothesis, the schedule machine after $t+1$ steps is the clock-stage encoding of that configuration. One more schedule step corresponds to one masked-machine step by `clockStageCfg_step`, using the current state $q$. The successor-run identity `runFrom_succ_eq_step'` identifies these one-step transitions with the runs at times $t+2$ and $t+1$, respectively, completing the induction.

**Key facts.** `Complexity.clockStageCfg_init`, `Complexity.clockStageCfg_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
