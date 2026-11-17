<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Tensorization.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.lengthVector_restrictLast_noiseOp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction of a noised combined vector

**Claim.** Restricting the noise images of the main function and auxiliary tuple at a bit gives the combined vector of their noise images after last-coordinate averaging, plus the sign of the bit times the noise parameter times the corresponding vector for their last-coordinate half-differences.

**Proof.** The restriction of a noise image decomposes as the noise image of the last-coordinate average plus the product of the bit's sign and the noise parameter with the noise image of the last-coordinate half-difference (`restrictLast_noiseOp_eq`). Use this identity for the main function and each auxiliary function. Linearity of the combined vector (`lengthVector_linear_combination`) then combines these coordinatewise decompositions into the asserted vector identity; the coefficient $1$ on the average terms simplifies away.

**Key facts.** `BooleanAnalysis.GaussianSpace.restrictLast_noiseOp_eq`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.lengthVector_linear_combination`.
