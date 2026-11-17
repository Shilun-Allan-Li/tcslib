<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopFuel_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Loop Fuel Configuration

**Claim.** For finite Boolean machines $B$ and $F$ and any Boolean input $x$, the initial configuration of the loop-fuel source machine equals the loop-fuel configuration built from the initial configuration of $F$ on $x$.

**Proof.** Compare the configuration fields. The initial state, input-head position, and output agree directly: both configurations use the initial state of $F$, the initial input position, and the empty output. For the work tapes, split their indices according to the nested right extensions that build the loop-fuel configuration. The original $F$ tapes retain their initial contents, which are blank. Each added tape is also blank by the definition of the right extension, so the tape functions agree at every index and position. The head positions agree for the same reason: every initial head is at zero, including those on the added tapes. Hence the configurations are equal.
