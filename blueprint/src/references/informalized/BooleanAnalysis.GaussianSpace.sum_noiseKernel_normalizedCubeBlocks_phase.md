<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BooleanCharacteristic.lean :: BooleanAnalysis.GaussianSpace.sum_noiseKernel_normalizedCubeBlocks_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block Noise Phase Identity

**Claim.** The normalized Boolean-cube phase sum over vectors of length $nm$ factors into the product, over blocks, of the one-coordinate correlated-sign characteristic raised to the $m$th power.

**Proof.** First, the phase decomposition for normalized blocks (`BooleanAnalysis.GaussianSpace.phase_normalizedCubeBlocks`) rewrites the exponent as a sum over the individual coordinates: coordinate $r$ contributes the two signs from its block, each scaled by $1/\sqrt m$. Apply the noise-kernel phase identity (`BooleanAnalysis.GaussianSpace.sum_noiseKernel_phase`) to the resulting cube sum, using coefficients $a_i/\sqrt m$ and $b_i/\sqrt m$ for the block containing each coordinate. The product is now over the $nm$ coordinates. Reindex those coordinates by pairs consisting of a block and a position within it; the finite product then groups by block. For each block the same characteristic factor occurs $m$ times, so its contribution is the $m$th power, yielding the claimed product.

**Key facts.** `BooleanAnalysis.GaussianSpace.phase_normalizedCubeBlocks`, `BooleanAnalysis.GaussianSpace.sum_noiseKernel_phase`.
