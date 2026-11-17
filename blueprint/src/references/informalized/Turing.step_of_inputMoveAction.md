<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.step_of_inputMoveAction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step from an Input-Only Action

**Claim.** If the transition from a configuration in state $q$ is the specified input-only action, then one step enters state $q'$ and moves the input head by $m$ with boundary clamping.

**Proof.** Since the configuration has state $q$, its step applies the transition prescribed for $q$. The transition hypothesis identifies that action as one which moves the input head by $m$, leaves every work tape and work-tape head unchanged, emits no output, and enters $q'$. Unfolding the one-step update therefore gives exactly the configuration with state $q'$ and input-head position moved by $m$; the work tapes, work-head positions, and output remain as before.
