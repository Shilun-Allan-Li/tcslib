<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_spaceUsedByTape_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space on One Tape Under Composition

**Claim.** For each work tape, the number of distinct cells visited in the composed run is at most the sum of the numbers visited in the two component runs.

**Proof.** The visited-cell inclusion theorem (`seamCompTM_visitedByTapeHead`) places every cell visited in the composed run inside the union of the cells visited in the two component runs. Taking cardinalities preserves this inclusion inequality, and the cardinality of a union is at most the sum of the two cardinalities. These facts give the claimed bound.

**Key facts.** `Turing.seamCompTM_visitedByTapeHead`.
