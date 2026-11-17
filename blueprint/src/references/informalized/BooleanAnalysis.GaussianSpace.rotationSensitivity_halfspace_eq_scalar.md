<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.rotationSensitivity_halfspace_eq_scalar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halfspace Sensitivity Reduces to One Dimension

**Claim.** For a unit vector $a$ and threshold $t$, the rotation sensitivity of the corresponding halfspace equals the probability that two correlated standard Gaussian scalars disagree at the threshold.

**Proof.** Project each of the two independent standard Gaussian vectors onto $a$, obtaining their scalar coordinates. The measure-preserving Gaussian projection theorem says each projection has standard Gaussian law (measurePreserving_gaussianProjection); applying it to both coordinates shows their joint law is the product of two standard Gaussian measures. The scalar disagreement event is measurable (measurableSet_scalar_rotation_disagreement), so the product measure of its preimage under these projections equals the scalar event's measure. Finally, linearity of the projection gives the rotated projection as $\cos\theta$ times the first scalar projection plus $\sin\theta$ times the second. Thus the preimage event is exactly the halfspace disagreement event defining rotation sensitivity, and taking the real-valued measure yields the claimed equality.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianProjection`, `BooleanAnalysis.GaussianSpace.measurableSet_scalar_rotation_disagreement`.
