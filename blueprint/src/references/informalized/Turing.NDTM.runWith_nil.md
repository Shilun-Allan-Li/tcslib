<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.runWith_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run on the Empty Choice Word

**Claim.** For every configuration on a fixed input, the run under the empty choice word returns that same configuration.

**Proof.** By the defining equation for a run, the empty choice word performs no steps and returns the starting configuration.
