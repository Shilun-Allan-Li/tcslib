<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.clearTM_spaceUsedByTape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space used while clearing a tape

**Claim.** At every time, the clearing machine visits at most $|w_i|+2$ distinct cells on the selected tape, and exactly one distinct cell on each other tape.

**Proof.** For the selected tape, use the trace description (`catalog_clear_trace`) with the initialized configuration. Its explicit forward and return phases place the head between positions $-1$ and $|w_i|$ relative to its starting position. The space bound for a head confined to this interval is $|w_i|+2$ cells (`catalog_space_bound`). For any other tape, the trace leaves its head at its initial position at every time. A constant head position visits exactly one distinct cell (`catalog_space_one`).

**Key facts.** `Turing.catalog_clear_trace`, `Turing.catalog_space_bound`, `Turing.catalog_space_one`.
