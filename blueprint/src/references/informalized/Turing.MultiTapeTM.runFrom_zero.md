<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.runFrom_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running zero steps

**Claim.** Running the machine for zero steps from a configuration leaves it unchanged.

**Proof.** The zeroth iterate of any function is the identity function. Since a run is defined by iterating the step function, a run of length zero returns the initial configuration.
