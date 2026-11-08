<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_gaussianNeg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian invariance under negation

**Claim.** Coordinatewise negation preserves the product standard Gaussian measure.

**Proof.** For each coordinate, negation sends a standard Gaussian law to itself: negating a Gaussian changes its mean to the negative of the original mean and leaves its variance unchanged, so the centered standard Gaussian is invariant. The coordinate negation maps are measurable, and the product measure preservation criterion then shows that their coordinatewise product preserves the full product law.
