<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_mapSetup_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setup head positions

**Claim.** After any number of steps in non-forward setup mode, every simulated work-tape head remains at position $0$.

**Proof.** Proceed by induction on $t$. At time $0$, the initial configuration places every work-tape head at $0$. For the induction step, the run at time $t+1$ is one step from the run at time $t$ (the successor-time description of iteration, `Turing.MultiTapeTM.runFrom_succ_eq_step'`). The setup-step invariance lemma (`Turing.FinTM.a2_mapSetup_head_step`) says that this step preserves the position of each simulated work-tape head. The induction hypothesis therefore gives position $0$ at time $t+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.a2_mapSetup_head_step`.
