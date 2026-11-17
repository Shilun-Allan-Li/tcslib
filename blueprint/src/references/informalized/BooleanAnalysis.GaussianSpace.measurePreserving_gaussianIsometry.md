<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_gaussianIsometry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian invariance under isometries

**Claim.** An orthogonal isometry of Euclidean $n$-space preserves the product standard Gaussian measure, viewed on coordinate vectors.

**Proof.** First identify coordinate vectors with Euclidean space using the standard $L^2$ equivalence. This identification sends the product Gaussian measure to its corresponding measure on Euclidean space, so it preserves measure in both directions. The given isometry preserves that Euclidean Gaussian measure by the previously established isometry result (`measurePreserving_gaussianEuclideanIsometry`). Conjugating the isometry by the coordinate-to-Euclidean identification therefore yields the stated coordinate-space map, and composition of these measure-preserving maps proves the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEuclideanIsometry`.
