<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Torus.lean :: BooleanAnalysis.GaussianSpace.surjective_gaussianTorus_pullback -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Surjectivity of Gaussian Torus Pullback

**Claim.** For the stated torus map and measure, every element of the target $L^p$ space is the pullback of an element of the source $L^p$ space.

**Proof.** Take an arbitrary $L^p$ function on the Euclidean space. The torus map is a measurable embedding (`measurableEmbedding_gaussianTorusMap`), so the function has a measurable extension to the torus agreeing with its pullback along the embedding. The embedding's measure-change property identifies the extension's $L^p$ integrability under the pushforward measure with the original function's integrability. Regard that extension as an element of the torus $L^p$ space. Pulling it back gives the original function almost everywhere, and therefore gives the same element of $L^p$.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurableEmbedding_gaussianTorusMap`.
