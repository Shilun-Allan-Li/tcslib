<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianThresholds.lean :: FABL.measurableSet_gaussianLowerLeftQuadrant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the Lower-Left Quadrant

**Claim.** The set of points in the plane equipped with the $\ell^2$ norm whose two coordinates are both nonpositive is measurable.

**Proof.** Each coordinate function on the plane is continuous (`FABL.continuous_correlationFirstCoordinate` and `FABL.continuous_correlationSecondCoordinate`). For a continuous real-valued function, the set where it is at most the constant zero is closed. The lower-left quadrant is the intersection of these two closed sublevel sets, hence is closed and therefore measurable.

**Key facts.** `FABL.continuous_correlationFirstCoordinate`, `FABL.continuous_correlationSecondCoordinate`.
