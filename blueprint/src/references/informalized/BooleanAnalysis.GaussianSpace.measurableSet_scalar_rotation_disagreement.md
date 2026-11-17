<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.measurableSet_scalar_rotation_disagreement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of Scalar Rotation Disagreement

**Claim.** For fixed $t$ and $\theta$, the set of pairs for which exactly one of the two stated scalar inequalities holds is measurable.

**Proof.** Each inequality defines a measurable subset of $\mathbb R^2$: the first uses the continuous first-coordinate projection, and the second uses the continuous function $(x,y)\mapsto \cos(\theta)x+\sin(\theta)y$. The disagreement set is the symmetric difference of these two measurable sets, hence is measurable.
