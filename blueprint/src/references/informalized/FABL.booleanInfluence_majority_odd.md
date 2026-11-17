<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.booleanInfluence_majority_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of odd-dimensional majority

**Claim.** For every nonnegative integer $m$ and coordinate $i$ of the $(2m+1)$-dimensional cube, the influence of majority is $\binom{2m}{m}/2^{2m}$.

**Proof.** The influence is the fraction of edges in direction $i$ across which majority changes (`booleanInfluence_eq_dimensionEdgeBoundaryFraction`). Removing that coordinate identifies such edges with inputs on a $(2m)$-dimensional cube. The majority boundary criterion says that an edge changes the output exactly when the remaining input has precisely $m$ positive coordinates (`isBoundaryDimensionEdge_majority_odd_iff`). The number of such inputs is $\binom{2m}{m}$ out of $2^{2m}$ equally likely inputs, by the positive-coordinate counting formula (`uniformProbability_positiveCoordinateCount_eq`).

**Key facts.** `FABL.booleanInfluence_eq_dimensionEdgeBoundaryFraction`, `FABL.isBoundaryDimensionEdge_majority_odd_iff`, `FABL.uniformProbability_positiveCoordinateCount_eq`.
