<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.card_reindexedJuntaWitnessCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on reindexed witness coordinates

**Claim.** The number of reindexed coordinates outside $P$ whose original indices lie in $J$ is at most $|J|$.

**Proof.** Map each reindexed coordinate to its original index outside $P$. By the definition of the selected family, every member maps into $J$. This map is injective: if two reindexed coordinates have the same original index, the corresponding elements of the subtype of indices outside $P$ are equal, and the equivalence used to reindex them then forces the coordinates themselves to be equal. Thus the selected family injects into $J$, so its cardinality is at most $|J|$.
