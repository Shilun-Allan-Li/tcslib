<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_spaceUsed_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Space Under Composition

**Claim.** The total number of visited work-tape cells, summed over all tapes, in the composed run is at most the sum of the total counts for the two component runs.

**Proof.** For each tape, the one-tape space bound (`seamCompTM_spaceUsedByTape_le_add`) bounds the composed run’s count by the sum of the corresponding two counts. Summing these inequalities over all work-tape indices gives the result: the sum of the two per-tape totals is the sum of the two total-space quantities.

**Key facts.** `Turing.seamCompTM_spaceUsedByTape_le_add`.
