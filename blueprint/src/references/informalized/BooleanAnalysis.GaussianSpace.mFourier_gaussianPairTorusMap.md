<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/UniformTransfer.lean :: BooleanAnalysis.GaussianSpace.mFourier_gaussianPairTorusMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Character of the Paired Torus Map

**Claim.** The Fourier character of the paired torus image of a pair of vectors is the exponential of the sum of their respective frequency pairings.

**Proof.** The character on the torus indexed by the disjoint union factors as the product of the characters on its two copies. Apply the Fourier formula for the Gaussian torus map to each copy: the first contributes the exponential of the frequency pairing with the first vector, and the second contributes the exponential of the frequency pairing with the second vector. Since the product of complex exponentials is the exponential of the sum of their exponents, the result follows. Expanding the frequency definition gives the stated coordinate expression.

**Key facts.** `BooleanAnalysis.GaussianSpace.mFourier_gaussianTorusMap`.
