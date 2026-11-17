<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianPolar.lean :: BooleanAnalysis.ThresholdFunctions.measurableSet_twoHalfplaneAngles -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the Two-Half-Plane Angle Set

**Claim.** For every real $\alpha$, the set of angles $\theta$ satisfying both $\cos\theta\leq0$ and $\cos(\theta-\alpha)\leq0$ is measurable.

**Proof.** The cosine function is continuous, so the set where $\cos\theta\leq0$ is measurable as a sublevel set of a measurable function. The map $\theta\mapsto\theta-\alpha$ is continuous, hence its composition with cosine is continuous and its nonpositive sublevel set is measurable as well. The set in question is the intersection of these two measurable sets, and is therefore measurable.
