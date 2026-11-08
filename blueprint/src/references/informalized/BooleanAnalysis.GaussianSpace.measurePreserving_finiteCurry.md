<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/BooleanBlocks.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_finiteCurry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure Preservation Under Finite Currying

**Claim.** Currying an array indexed by a finite product preserves the product measure when the target space has measurable singletons and each coordinate measure is sigma-finite.

**Proof.** The currying equivalence is measurable. To show that it preserves measure, it suffices to compare the measures of singleton sets, since the measures involved are finite product measures on a space with measurable singletons. The preimage of the singleton containing an array $x$ is the singleton containing its uncurried array: currying and uncurrying are inverse operations. The product-measure formula for rectangles then evaluates the source and target singleton measures as products of the same coordinate singleton measures. Reordering the finite product does not change its value, so these measures agree. Hence the currying equivalence preserves the product measure.
