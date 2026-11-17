<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCount_idle_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Configurations Stay Fixed

**Claim.** For every bit-list input, every configuration of the increment machine in the return state, and every natural number $t$, running the machine for $t$ steps leaves the configuration unchanged.

**Proof.** Induct on $t$. At zero steps the run is the starting configuration. For the successor case, the run law expresses the run as first taking one step and then running for the preceding number of steps (`Turing.MultiTapeTM.runFrom_succ_eq_step`). The one-step return-state result says that this first step fixes the configuration (`Complexity.clCount_idle`); the induction hypothesis then says the remaining run also fixes it.

**Key facts.** `Complexity.clCount_idle`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
