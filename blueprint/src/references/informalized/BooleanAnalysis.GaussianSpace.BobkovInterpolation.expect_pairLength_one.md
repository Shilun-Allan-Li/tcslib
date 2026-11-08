<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Tensorization.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.expect_pairLength_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noisy Last-Coordinate Splitting

**Claim.** The uniform expectation of the pair length at the stated noisy inputs and clock equals the average of the extended functionals on the two last-coordinate restrictions, with the difference function included as an additional coordinate.

**Proof.** Fix a point $x$ in the lower-dimensional cube. The squared length vector on either last-coordinate slice decomposes into the sum of squared derivatives in the first $n$ coordinates and the squares of the listed additional functions (`sum_sq_lengthVector`). The restriction formula for the noise operator says that the noisy value on a slice is its noisy average plus or minus its noisy difference (`noiseOp_restrictLast_eq`); the two signs are $+1$ for the false slice and $-1$ for the true slice (`boolToSign_false`, `boolToSign_true`). Substituting these identities into the two radicands of the pair length identifies them with the radicands of the extended functionals on the respective slices, each with the noisy difference as the new first vector coordinate. Thus the pointwise pair length is their average. Averaging over $x$ and distributing the finite sum over this average gives the claimed expectation identity.

**Key facts.** `BooleanAnalysis.GaussianSpace.BobkovInterpolation.sum_sq_lengthVector`, `BooleanAnalysis.GaussianSpace.noiseOp_restrictLast_eq`, `BooleanAnalysis.boolToSign_false`, `BooleanAnalysis.boolToSign_true`.
