<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.NDTM.stepWith_of_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step from a Specified State

**Claim.** If a configuration has state $q$, its next configuration under choice $b$ is obtained by applying the action prescribed by the transition function at $q$ to that configuration.

**Proof.** Unfold the definition of a step, which branches on the configuration's state. Substituting the given equality that the state is $q$ selects the nonhalting branch. That branch applies the action prescribed by the transition function at $q$, using the input symbol and work-tape symbols scanned in the configuration, as claimed.
