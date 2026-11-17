<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferedFirstCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-phase lockstep simulation

**Claim.** If the first machine has not halted at any time before $t$, then the buffered composition run for $t$ steps from the first-phase embedding of $c$ is the first-phase embedding of the first machine's configuration after $t$ steps.

**Proof.** Proceed by induction on $t$. At $t=0$, both runs are their starting configurations, so the claim is immediate. For the successor case, first express each run of length $t+1$ as one step applied after its run of length $t$. The induction hypothesis identifies the buffered run at time $t$ with the embedding of the first machine's run at time $t$. The hypothesis that the first machine has not halted before time $t+1$ ensures that this configuration is active at time $t$. The single-step simulation lemma (`bufferedFirstCfg_step`) therefore identifies the next buffered step with the embedding of the first machine's next configuration. Rewriting the runs once more as successor runs gives the result.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.bufferedFirstCfg_step`.
