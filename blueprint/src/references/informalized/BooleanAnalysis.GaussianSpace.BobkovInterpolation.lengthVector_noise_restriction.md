<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Tensorization.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.lengthVector_noise_restriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise and last-coordinate restriction

**Claim.** The combined vector made from the noise images of the restrictions at a bit equals the combined vector of the noise images of the last-coordinate averages, plus the bit's sign times the corresponding combined vector for the last-coordinate half-differences.

**Proof.** The noise image of a restriction at a fixed bit decomposes pointwise as the noise image of the last-coordinate average plus the sign of that bit times the noise image of the last-coordinate half-difference (`noiseOp_restrictLast_eq_fun`). Apply this identity to the main function and to each auxiliary function. The resulting combined vector is therefore the combined vector of the sum of these two families, with coefficients $1$ and the bit's sign. Linearity of the combined vector (`lengthVector_linear_combination`) identifies it with the stated sum; the coefficient $1$ leaves the first vector unchanged.

**Key facts.** `BooleanAnalysis.GaussianSpace.noiseOp_restrictLast_eq_fun`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.lengthVector_linear_combination`.
