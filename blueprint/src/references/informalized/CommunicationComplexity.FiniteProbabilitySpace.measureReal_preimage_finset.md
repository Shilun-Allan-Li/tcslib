<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.measureReal_preimage_finset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure of a finite-set preimage

**Claim.** For a map from a finite probability space to a discrete measurable space, the probability of the preimage of a finite set is the sum, over its points, of the probabilities of their singleton preimages.

**Proof.** The preimage of the finite set is the union, indexed by its points, of the singleton preimages. These preimages are pairwise disjoint: distinct target points cannot be the image of the same source point. They are measurable because the source space is discrete. Finite additivity thus expresses the extended-real measure of the union as the sum of the individual measures. Each term is finite since it is bounded by the measure of the whole probability space, so conversion to real values distributes over this finite sum. The resulting equality is the claimed formula.
