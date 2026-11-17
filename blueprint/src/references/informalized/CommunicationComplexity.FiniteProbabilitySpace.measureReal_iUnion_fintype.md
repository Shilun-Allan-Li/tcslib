<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.measureReal_iUnion_fintype -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite additivity over disjoint unions

**Claim.** For a pairwise disjoint family of subsets indexed by a finite set, the real-valued measure of their union is the sum of their real-valued measures.

**Proof.** First express the real-valued measure as the real conversion of the underlying nonnegative extended-real measure. Countable additivity for pairwise disjoint measurable sets gives the measure of the union as the sum of the individual measures; every set is measurable because the space is discrete. Since the index set is finite, this sum is finite. Each summand is finite as well, being bounded by the measure of the whole probability space. The real conversion therefore carries the finite sum to the sum of the real conversions, yielding the claimed equality.
