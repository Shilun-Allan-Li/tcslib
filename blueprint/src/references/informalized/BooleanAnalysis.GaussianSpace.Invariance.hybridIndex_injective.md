<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Sequence.lean :: BooleanAnalysis.GaussianSpace.Invariance.hybridIndex_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of hybrid coordinate selection

**Claim.** The map that sends coordinate $i$ to the right copy when $i<r$ and to the left copy otherwise is injective.

**Proof.** Suppose two coordinates have the same image. If both satisfy the threshold condition, their images are in the right copy and equality there forces the coordinates themselves to be equal. If neither satisfies it, equality in the left copy likewise forces equality. If exactly one satisfies the condition, the images lie in different summands of the disjoint union and cannot be equal. Hence the original coordinates are equal in every possible case.
