<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.length_prevSnapSrcs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Previous Snapshot Source Length

**Claim.** For every time $t$, the list of bit sources defined for the previous snapshot has length equal to the number of possible snapshots of $M$.

**Proof.** The list is obtained by mapping one source for each index in the range from zero up to, but not including, the snapshot count. Each index contributes exactly one entry, whether the entry is a constant for time zero or a block source otherwise. Its length is therefore the length of that range, namely the number of possible snapshots.
