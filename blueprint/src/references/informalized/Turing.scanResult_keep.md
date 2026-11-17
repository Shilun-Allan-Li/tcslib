<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.scanResult_keep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Keep Scan

**Claim.** A second pass that preserves both state and symbols leaves the state and word produced by the first pass unchanged.

**Proof.** The second pass starts with the final state of the first pass and reads the first output word in reverse. A keep transition preserves its state and returns each symbol unchanged, so running it on any word returns that same state and word (`Turing.mealyRun_keep`). Reversing the resulting word therefore recovers the first pass's output word, and the overall pair equals the first-pass result.

**Key facts.** `Turing.mealyRun_keep`.
