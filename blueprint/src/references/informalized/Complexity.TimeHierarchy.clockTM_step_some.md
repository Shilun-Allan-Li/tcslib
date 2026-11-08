<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.clockTM_step_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock Machine Step Rule

**Claim.** When the clock machine configuration has state $q$, its next configuration is obtained by applying the clock transition prescribed for $q$ and the symbols currently scanned.

**Proof.** Unfold the definition of a machine step. Since the configuration’s state is the given state $q$, the step is the transition action for $q$, applied to that configuration. This is exactly the asserted equality.
