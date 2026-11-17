<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.controlCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Controller simulation before halting

**Claim.** If the run of $D$ from $c$ is nonhalting at every time before $t$, then the conditional machine run for $t$ steps from the embedded controller configuration equals the embedding of the configuration reached by running $D$ for $t$ steps.

**Proof.** Proceed by induction on $t$. At time zero, both sides are the same embedded starting configuration. For the successor step, the induction hypothesis identifies the conditional machine's configuration after $t$ steps with the embedding of $D$'s configuration at time $t$. The hypothesis on the run ensures that this configuration of $D$ is still nonhalting. Thus the one-step controller simulation lemma (`controlCfg_step`) applies: one more step of the conditional machine gives exactly the embedding of one step of $D$. The successor-time formula for runs (`runFrom_succ_eq_step'`) identifies these one-step extensions with the runs of length $t+1$, proving the claim.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.controlCfg_step`.
