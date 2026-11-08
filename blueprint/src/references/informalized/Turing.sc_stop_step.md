<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_stop_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stopping state triggers a finish step

**Claim.** If the body state satisfies the stopping predicate, one step of the clocked machine from the forward counting phase enters the corresponding finish state and leaves the body configuration and clock data unchanged.

**Proof.** In the clocked machine's transition rule, a configuration in the decrement phase with forward flag and a state satisfying the stopping predicate takes the special stopping branch. That branch makes no input or work-tape movement and writes nothing, while setting the successor state to the finish state carrying the same body state. Applying this action therefore preserves the body configuration, clock tape, and clock-head position, as claimed.
