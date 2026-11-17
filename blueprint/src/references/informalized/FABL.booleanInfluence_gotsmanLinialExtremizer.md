<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.booleanInfluence_gotsmanLinialExtremizer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of the Gotsman–Linial extremizer

**Claim.** For nonnegative integers $m,k$ and any coordinate of the $(m+1)$-dimensional cube, the influence of the Gotsman–Linial extremizer with parameters $m+1,k$ is the stated sum of binomial coefficients divided by $2^m$.

**Proof.** If $k=0$, the defining polynomial is the empty product, hence constant; the function is constant and has no pivotal inputs, while the displayed sum is empty. For $k=s+1$, identify an edge in the chosen coordinate direction with its remaining $m$ coordinates. The extremizer has a boundary edge precisely when the positive-coordinate count among those remaining coordinates equals its starting count plus some $j<s+1$ (`isBoundaryDimensionEdge_gotsmanLinialExtremizer_succ_iff`). The influence equals the fraction of edges in that direction that are boundary edges (`booleanInfluence_eq_dimensionEdgeBoundaryFraction`), so it is the uniform probability of this positive-count event. Counting cube points with each specified positive-coordinate count gives the sum of binomial probabilities (`uniformProbability_exists_positiveCoordinateCount_eq_add`), yielding the formula.

**Key facts.** `FABL.booleanInfluence_eq_dimensionEdgeBoundaryFraction`, `FABL.isBoundaryDimensionEdge_gotsmanLinialExtremizer_succ_iff`, `FABL.uniformProbability_exists_positiveCoordinateCount_eq_add`.
