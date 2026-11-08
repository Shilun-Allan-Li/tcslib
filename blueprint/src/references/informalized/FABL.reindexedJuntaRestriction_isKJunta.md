<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.reindexedJuntaRestriction_isKJunta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Junta Property of a Reindexed Restriction

**Claim.** If $f$ depends only on coordinates in $J$ and $|J|\le k$, then fixing the coordinates in $P$ and reindexing the remaining coordinates yields a $k$-junta.

**Proof.** Use the reindexed witness coordinates associated to $P$ and $J$ as the junta support. Their number is at most $|J|$ by the cardinality bound for these witness coordinates (`FABL.card_reindexedJuntaWitnessCoordinates_le`), hence at most $k$. To show dependence only on this support, take two reindexed inputs agreeing on the witness coordinates and compare the corresponding full assignments to the original function. For each coordinate $i\in J$, if $i\in P$, both full assignments use the same fixed sign $z(i)$. If $i\notin P$, the coordinate corresponds, under the reindexing equivalence, to a witness coordinate; the two inputs agree there, so the full assignments agree at $i$ as well. Thus the full assignments agree on all of $J$, and the hypothesis that $f$ depends only on $J$ gives equal function values. This proves the junta property.

**Key facts.** `FABL.card_reindexedJuntaWitnessCoordinates_le`.
