<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Rotation.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_gaussianRotation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rotation invariance of paired Gaussian vectors

**Claim.** The planar rotation by $t$, applied coordinatewise to a pair of vectors in $\mathbb R^n$, preserves their product standard Gaussian measure.

**Proof.** On each scalar coordinate pair, the rotation is measurable and preserves the product of two standard Gaussian laws: a centered Gaussian vector with identity covariance is invariant under orthogonal rotations, expressed here by the Gaussian rotation identity (`ProbabilityTheory.IsGaussian.map_rotation_eq_self`). Reindex the space of two vectors as the space whose coordinates are scalar pairs. The product measure preservation criterion applies the scalar rotation independently at every coordinate, so it preserves the resulting product measure. Finally, undo the reindexing on the input and output; these coordinate rearrangements preserve the corresponding product measures. Their composition is precisely the coordinatewise planar rotation in the statement.
