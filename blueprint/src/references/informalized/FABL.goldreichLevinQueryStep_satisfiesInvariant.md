<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinQueryStep_satisfiesInvariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Invariant Preservation

**Claim.** If the current query state satisfies the active-family invariant at stage $k$, and the appended estimate trace is accurate and covers every candidate at stage $k+1$, then one query step produces a state satisfying the invariant at stage $k+1$.

**Proof.** Choose the active family witnessing the current state invariant, and append the new records to the state trace. The coverage assumption for the new records also gives coverage by the appended trace, since every new record belongs to that trace. The old active family is supported on the first $k$ coordinates, so every candidate obtained by adding or omitting coordinate $k$ is supported on the first $k+1$ coordinates (`goldreichLevinCandidates_subset_prefixCoordinates_succ`). The trace accuracy and this candidate coverage imply that the trace estimator is accurate on every candidate needed at this stage (`goldreichLevinTraceEstimate_accurate_of_mem`). Apply the stage-accuracy results: refinement returns the retained family rather than failure (`goldreichLevinRefine_eq_some_retained_of_stageAccurate`), that family satisfies the active invariant at stage $k+1$ (`goldreichLevinActiveInvariant_retained`), and its size is at most the prescribed active cap (`card_goldreichLevinRetained_le_activeCap_of_stageAccurate`). The query-step definition uses precisely this appended trace and refinement, so its resulting state has the retained family as its active family, establishing the required state invariant.

**Key facts.** `FABL.goldreichLevinCandidates_subset_prefixCoordinates_succ`, `FABL.goldreichLevinTraceEstimate_accurate_of_mem`, `FABL.goldreichLevinRefine_eq_some_retained_of_stageAccurate`, `FABL.goldreichLevinActiveInvariant_retained`, `FABL.card_goldreichLevinRetained_le_activeCap_of_stageAccurate`.
