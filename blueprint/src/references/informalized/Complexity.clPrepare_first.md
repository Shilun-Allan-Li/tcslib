<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPrepare_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Arrival at the Prepared Configuration

**Claim.** The preparation machine reaches the specified loading configuration within the stated bound, at a positive time, and never occupies the loader’s final-counter entry state earlier.

**Proof.** The completion result (`Complexity.clPrepare_complete`) supplies a time $B$ within the stated bound at which the machine is in the specified loading configuration. That configuration has the loader’s final-counter entry state. Apply the first-arrival principle (`Complexity.clFirst`) to this run: the initial configuration is not in that state, and once the machine reaches that state its step leaves the whole configuration fixed (`Complexity.clPrepare_idle`). The principle therefore selects a positive time $t\le B$ at which the target configuration is reached and at every earlier time the state differs from the target state. Since $B$ already satisfies the desired upper bound, so does $t$.

**Key facts.** `Complexity.clPrepare_complete`, `Complexity.clFirst`, `Complexity.clPrepare_idle`.
