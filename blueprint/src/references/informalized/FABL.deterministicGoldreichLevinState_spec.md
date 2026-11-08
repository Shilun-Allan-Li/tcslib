<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinState_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin State Invariant

**Claim.** For every stage $k\le n$, the recursively constructed state satisfies the active-family invariant and its trace consists entirely of accurate estimates.

**Proof.** Proceed by induction on the stage. At stage zero, the initial state has active family $\{\varnothing\}$ and empty trace. The initial-state invariant gives the required family properties, while the empty trace makes the accuracy condition immediate.

For the successor stage $k+1\le n$, the induction hypothesis gives an invariant active family at stage $k$ and accuracy of all estimates already recorded. The stage-record accuracy result says every newly generated estimate is accurate; hence every record in the concatenated trace is accurate. The coverage result ensures that the new records include an estimate for each candidate produced by extending the current active family at coordinate $k$. The query-step invariant theorem applies to the previous state, this accurate concatenated trace, and this coverage, yielding the active-family invariant at stage $k+1$. The recursive state definition takes exactly this query step: the induction bound ensures $k<n$, the previous active family is the one supplied by the invariant, and its cardinality satisfies the required cap. Its trace is the concatenation just shown accurate. This proves both assertions at the successor stage.

**Key facts.** `FABL.goldreichLevinInitialQueryState_satisfiesInvariant`, `FABL.deterministicGoldreichLevinStageRecords_isAccurate`, `FABL.deterministicGoldreichLevinStageRecords_covers`, `FABL.goldreichLevinQueryStep_satisfiesInvariant`.
