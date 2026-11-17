<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureProbability_reindexBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Reindexing Invariance

**Claim.** Reindexing the coordinates of a Boolean function along a bijection preserves its coordinate-switching failure probability, for every parameter and threshold.

**Proof.** The probability is a finite sum over all assignments of the three restriction states to the coordinates. Reindex these assignments along the coordinate bijection; this is a bijection of the finite indexing sets, so it preserves the sum. For corresponding assignments, the failure indicators agree under reindexing (\texttt{coordSwitchingFailureIndicator\_reindexBooleanFunction}), and the assignment weights agree because the coordinatewise product is unchanged by a permutation of factors (\texttt{restrictionAssignmentWeightAt\_reindex}). Hence the two sums are equal.

**Key facts.** `FABL.coordSwitchingFailureIndicator_reindexBooleanFunction`, `FABL.restrictionAssignmentWeightAt_reindex`.
