<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_unary_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Normalization Preserves Runs

**Claim.** Reinterpreting the configuration reached after $t$ steps of the normalized machine from $c$ gives the configuration reached after $t$ steps of $M$ from the unary reinterpretation of $c$.

**Proof.** Induct on $t$, with the starting configuration arbitrary. At zero steps, both sides are the unary reinterpretation of $c$. For the successor case, express a run of $t+1$ steps as one step followed by a run of $t$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step`). The one-step correspondence (`Complexity.b2_unary_step`) identifies the reinterpreted successor with the successor from the reinterpreted configuration. Apply the induction hypothesis to these successor configurations, then express the resulting run again as a run of $t+1$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.b2_unary_step`.
