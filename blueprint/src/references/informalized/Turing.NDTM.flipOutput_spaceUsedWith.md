<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.NDTM.flipOutput_spaceUsedWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output flipping preserves space use

**Claim.** Flipping every output bit in the starting configuration and using the machine with flipped output leaves the space used during a run unchanged.

**Proof.** Space use is the sum, over work tapes, of the number of distinct head positions visited while running prefixes of the choice word. For each prefix, the run with flipped output from the flipped configuration is the flipped version of the original prefix-run result (Turing.NDTM.flipOutput_runWith). Flipping a configuration changes only its output, so each corresponding work-tape head position is identical. Hence the sets of visited positions, their cardinalities, and their sum are unchanged.

**Key facts.** `Turing.NDTM.flipOutput_runWith`.
