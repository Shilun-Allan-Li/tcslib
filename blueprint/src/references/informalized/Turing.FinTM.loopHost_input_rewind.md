<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_input_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind from Controller Phase Four

**Claim.** From any host configuration in controller phase $4$, there is a number of steps bounded by the input-head position plus $2$ after which the host has the same configuration data except that it is in the startup body-call state with release clear and the body machine's initial state, and its input head is at position $1$.

**Proof.** The phase-$4$ transition is a leftward input move to phase $5$, with no work-tape or output changes. The phase-$5$ transition continues moving left while it reads an input symbol, and at the left boundary moves right into the specified startup body-call state. The identity `loopControl_idle` identifies these transitions with the standard control actions: first the leftward transition to the scan state, then the scan transition determined by whether the input symbol is present. Apply the bounded input-rewind result `loop_rewind_bounded` with start state phase $4$, scan state phase $5$, and the required destination. It supplies a time at most the initial input-head position plus $2$ and gives precisely the claimed configuration.

**Key facts.** `Turing.FinTM.loopControl_idle`, `Turing.FinTM.loop_rewind_bounded`.
