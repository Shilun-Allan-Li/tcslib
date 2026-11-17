<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_decExit_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the exit-state map

**Claim.** For a fixed state $s$, the map from counter phases to clock states that sends the completed true phase to the body state at $s$, the completed false phase to the timeout state carrying $s$, and every other phase to the decrement state carrying $s$ is injective.

**Proof.** Compare the images of two phases, splitting each phase into the running, rewind, or completed form, and in the completed case into its two Boolean verdicts. Distinct constructor families in the clock-state type cannot have equal outputs: decrement states, body states, and timeout states are separate constructors. Within the decrement family, equality forces the stored phases to agree; within the completed cases, the two verdicts lead to the distinct body and timeout constructors. Thus equality of images forces equality of the original phases.
