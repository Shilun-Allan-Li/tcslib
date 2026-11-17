<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.measurableSet_signQuadrant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of a Sign-Defined Quadrant

**Claim.** For any two signs $s,t\in\{-1,1\}$, the set of points $(x_0,x_1)\in\mathbb R^2$ satisfying $0\le s x_0$ and $0\le t x_1$ is measurable.

**Proof.** For fixed signs $s$ and $t$, each signed coordinate function is continuous. The set where either such function is at least zero is closed, since it is the inverse image of a closed half-line under a continuous function. The sign-defined quadrant is the intersection of these two closed sets, so it is closed and therefore measurable.
