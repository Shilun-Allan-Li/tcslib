<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.isOpen_gaussianUpperRightQuadrant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Openness of the upper-right quadrant

**Claim.** For every real $t$, the set of points in the correlation plane whose two coordinates are both greater than $t$ is open.

**Proof.** Each coordinate projection on the correlation plane is continuous. Consequently, the condition that the first coordinate be strictly greater than $t$ defines an open set, as does the corresponding condition on the second coordinate. Their intersection is precisely the upper-right quadrant above $t$, so it is open.

**Key facts.** `FABL.continuous_correlationFirstCoordinate`, `FABL.continuous_correlationSecondCoordinate`.
