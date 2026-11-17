<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/CodePrefix.lean :: Complexity.TimeHierarchy.preTM_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preprocessing Machine Step

**Claim.** If the configuration is in preprocessing state $q$, its next configuration is obtained by applying the action prescribed by the preprocessing transition function at $q$, using the symbols read from that configuration.

**Proof.** Unfold the machine’s step function. Since the configuration’s state is $\mathrm{some}(q)$, the step takes the transition prescribed at $q$ and applies it to the configuration. This is exactly the asserted equality.
