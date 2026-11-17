<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.ConfigCount.core_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evolution determined by the core

**Claim.** For configurations with equal cores, running the same machine for any fixed number of steps produces configurations with equal cores.

**Proof.** Induct on the number of steps. At time zero the claim is the assumed equality of cores. For the successor step, write each run of length $t+1$ as one step after a run of length $t$ (`runFrom_succ_eq_step'`). The induction hypothesis gives equal cores after the first $t$ steps, and the one-step preservation of core equality (`core_step`) gives equal cores after the next step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.ConfigCount.core_step`.
