<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lockstep folding simulation

**Claim.** After $t+1$ steps, the folding simulator started on the embedded input reaches the folded configuration obtained after $t$ steps of the original machine.

**Proof.** Proceed by induction on $t$. For $t=0$, one simulator step from its initial configuration produces the folded original initial configuration, by the initialization correspondence (`foldCfg_init`); the zero-step run is the starting configuration (`runFrom_zero`), and the successor-step description identifies the extra step. For the inductive step, write a run of length $t+1$ as one step after the run of length $t$ (`runFrom_succ_eq_step'`). By the induction hypothesis, the length-$t$ simulator run is the fold of the original length-$t$ run. The one-step correspondence says that stepping this folded configuration gives the fold of the original machine’s next configuration (`foldCfg_step`). The successor-step identity then identifies that result with the original run of length $t+1$, proving the claim for $t+1$.

**Key facts.** `Turing.FinTM.foldCfg_init`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.foldCfg_step`.
