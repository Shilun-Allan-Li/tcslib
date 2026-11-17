<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.catalog_redirect_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Redirect-State Loop Invariance

**Claim.** Every configuration of the redirected machine in its added loop state remains unchanged after any number of steps.

**Proof.** Induct on the number of steps. At time zero the run is the original configuration. For a successor time, the induction hypothesis reduces the run to taking one step from that configuration. In the added loop state, the redirected machine’s transition stays in that state, does not move the input head or any work-tape head, writes nothing, and emits nothing. Hence every component of the configuration is unchanged. The successor-time run is expressed as one step after the preceding run by the run recurrence (`MultiTapeTM.runFrom_succ_eq_step'`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
