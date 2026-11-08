<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean :: CommunicationComplexity.Rectangle.monoPartition_cross_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cross Closure of a Rectangle

**Claim.** If two input pairs lie in the same part of a monochromatic rectangle partition, then both crossed pairs also lie in that part.

**Proof.** Because $R$ is a member of the partition, the partition’s rectangle condition says that $R$ is a rectangle. The cross-closure characterization of rectangles (`IsRectangle_iff`) states that whenever $(x,y)$ and $(x',y')$ belong to a rectangle, both $(x',y)$ and $(x,y')$ belong to it as well. Applying it to the two given pairs proves the claim.

**Key facts.** `CommunicationComplexity.Rectangle.IsRectangle_iff`.
