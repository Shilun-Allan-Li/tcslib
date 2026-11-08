<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.isRelevantJuntaRestriction_of_reindexed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relevance of a Reindexed Junta Restriction

**Claim.** If the reindexed restriction has positive influence in coordinate $i$, then the original restricted function has two free-coordinate assignments differing only at the corresponding free coordinate on which its values differ.

**Proof.** Positive influence gives an assignment of the reindexed cube at which setting coordinate $i$ to $1$ or $-1$ produces different values (\texttt{FABL.isRelevant_iff_exists_setCoordinate_ne}). Let $y_0,y_1$ be the corresponding free assignments, obtained by identifying the reindexed cube with assignments to the free coordinates. Because the two reindexed inputs differ only in coordinate $i$, their free assignments agree at every other free coordinate: the indexing equivalence sends any such coordinate to an index other than $i$, where the coordinate update leaves the input unchanged. If the restricted function had equal values at $y_0,y_1$, applying the real-valued sign map would make the reindexed function's two values equal, contradicting the chosen witness. Hence these assignments establish relevance of the restriction at the corresponding free coordinate.

**Key facts.** `FABL.isRelevant_iff_exists_setCoordinate_ne`.
