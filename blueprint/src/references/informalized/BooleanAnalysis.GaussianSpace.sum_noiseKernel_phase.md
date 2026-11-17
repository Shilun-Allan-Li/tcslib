<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BooleanCharacteristic.lean :: BooleanAnalysis.GaussianSpace.sum_noiseKernel_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Kernel Phase Identity

**Claim.** The normalized sum over Boolean vector pairs of the noise-kernel-weighted complex phase equals the product of the correlated-sign characteristic factors, one for each coordinate.

**Proof.** For each coordinate $i$, define its local contribution to be the factor $(1+\rho\sigma(x_i)\sigma(y_i))/4$ times the complex phase $e^{i(a_i\sigma(x_i)+b_i\sigma(y_i))}$. The normalization $2^{-N}$, the coordinate factors of the noise kernel, and the exponential of the sum of coordinate phases combine into the product of these local contributions. The factorization of a Boolean coordinate sum (`BooleanAnalysis.GaussianSpace.sum_pair_coordinate_products`) then turns the sum over all vector pairs of this product into a product, over coordinates, of the two-sign-pair sums. Each such local sum is the correlated-sign phase formula (`BooleanAnalysis.GaussianSpace.sum_correlatedSign_phase`), giving the asserted product.

**Key facts.** `BooleanAnalysis.GaussianSpace.sum_pair_coordinate_products`, `BooleanAnalysis.GaussianSpace.sum_correlatedSign_phase`.
