<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_mapSetup_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement before simulation

**Claim.** If the non-forward run has not entered a state representing a simulated state of $M$ at any time before $t$, then the forward and non-forward mapping machines have identical configurations at time $t$.

**Proof.** Induct on $t$. At time $0$, both modes have the same initial configuration. For the successor step, the hypothesis for times below $t+1$ also excludes entry at every time below $t$, so the induction hypothesis identifies the two configurations at time $t$. It also excludes entry at time $t$ itself. Thus the shared configuration is outside the simulation states, and the setup-step agreement lemma (`Turing.FinTM.a2_mapSetup_step`) says the two modes have the same one-step successor there. Rewriting each run at time $t+1$ as one step from time $t$ (by `Turing.MultiTapeTM.runFrom_succ_eq_step'`) proves the desired equality.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.a2_mapSetup_step`.
