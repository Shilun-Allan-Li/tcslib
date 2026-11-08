<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.frontier_gaussianUpperRightQuadrant_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frontier of an upper quadrant

**Claim.** Every point on the frontier of the region where both coordinates exceed $t$ has at least one coordinate equal to $t$.

**Proof.** Write the region as the intersection of the two open half-planes defined by the first and second coordinate inequalities. Each coordinate function is continuous (continuity of the first coordinate, `FABL.continuous_correlationFirstCoordinate`, and of the second, `FABL.continuous_correlationSecondCoordinate`). Thus the frontier of each half-plane lies on its boundary line, where the corresponding coordinate equals $t$. The frontier of an intersection is contained in the union of the frontiers of the two sets. Applying this inclusion and then the two boundary-line containments gives the result.

**Key facts.** `FABL.continuous_correlationFirstCoordinate`, `FABL.continuous_correlationSecondCoordinate`.
