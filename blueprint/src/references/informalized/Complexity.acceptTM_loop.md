<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.acceptTM_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationarity of the Loop State

**Claim.** If a configuration of the halting recognizer has state equal to the loop state, then running the recognizer from that configuration for any natural number of steps leaves the configuration unchanged.

**Proof.** Proceed by induction on the number of steps. At zero steps the run is the original configuration. For the successor case, the successor-run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) expresses the run as one step from the result after the preceding number of steps. By the induction hypothesis that preceding run is the original configuration. Its state is the loop state, so the recognizer's transition in this state is a self-loop with no tape movement, writing, or output. Applying this transition therefore leaves every component of the configuration unchanged, proving the successor case.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
