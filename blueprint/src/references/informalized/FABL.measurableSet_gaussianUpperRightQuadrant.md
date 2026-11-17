<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianThresholds.lean :: FABL.measurableSet_gaussianUpperRightQuadrant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Measurability of an Upper-Right Region

**Claim.** For each real number $t$, the set of points in the plane equipped with the $\ell^2$ norm whose two coordinates are both greater than $t$ is measurable.

**Proof.** The two coordinate functions are continuous (`FABL.continuous_correlationFirstCoordinate` and `FABL.continuous_correlationSecondCoordinate`). The supplied proof constructs the intersection of the closed sets where each coordinate is at least $t$, and concludes that this intersection is measurable. However, those are non-strict inequalities, whereas the stated region uses strict inequalities. The proof as supplied therefore does not establish the stated claim: it proves measurability of the corresponding closed upper-right region. The strict upper-right region is also measurable, since it is the intersection of two open inverse images under continuous coordinate functions, but that is not the argument given in the proof source.

**Key facts.** `FABL.continuous_correlationFirstCoordinate`, `FABL.continuous_correlationSecondCoordinate`.

**Caveat.** The proof source uses closed non-strict coordinate inequalities, which do not match the formal definition’s strict inequalities.
