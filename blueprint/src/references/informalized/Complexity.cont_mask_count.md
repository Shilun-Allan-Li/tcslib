<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_mask_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission count and output length

**Claim.** The initial output length plus the number of true entries in the emission mask for the first $t$ steps equals the output length after those $t$ steps.

**Proof.** Induct on $t$, generalizing the starting configuration. At $t=0$, the mask is empty and the run has not changed the configuration, so the identity holds. For the successor case, the run for $t+1$ steps is the run for $t$ steps starting from the one-step successor (`Turing.MultiTapeTM.runFrom_succ_eq_step`). Apply the induction hypothesis there. The one-step output identity says that this successor's output is the old output followed by the optional symbol emitted at the current step (`Turing.MultiTapeTM.step_output`), so its length increases by one exactly when that symbol is present. The emission mask likewise prefixes the indicator of that event to the mask for the remaining steps. Whether the symbol is present or absent, both sides therefore acquire the same increment, proving the successor case.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.step_output`.
