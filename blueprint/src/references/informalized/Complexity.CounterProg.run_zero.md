<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.run_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Step Run

**Claim.** Running the program for zero steps from any state returns that state.

**Proof.** A zero-fold iterate of the one-step transition is the identity function. Thus applying it to the state returns the state unchanged.
