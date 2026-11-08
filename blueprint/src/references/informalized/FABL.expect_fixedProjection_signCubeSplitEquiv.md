<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.expect_fixedProjection_signCubeSplitEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average of a Fixed-Coordinate Projection

**Claim.** The average of a function of the coordinates outside $J$, evaluated on the restriction of a uniform sign assignment, equals the uniform average of that function over assignments to those coordinates.

**Proof.** Split each sign assignment into its restriction to $J$ and its restriction to the complement. The split is a bijection, so the original average becomes the average over pairs of such restrictions. Averaging first over the restriction to $J$ leaves the function unchanged, because it depends only on the complementary restriction. Its average over the first block is therefore the same function, and the remaining average is precisely the uniform average over assignments on the complement.
