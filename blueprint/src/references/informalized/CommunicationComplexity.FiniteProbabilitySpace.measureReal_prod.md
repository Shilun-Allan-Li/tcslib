<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.measureReal_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure of a product rectangle

**Claim.** Under the product probability measure, the measure of a rectangle is the product of the measures of its two coordinate sets.

**Proof.** The measure on the product space is the product of the two coordinate measures. The product-measure formula for rectangles identifies the extended-real measure of $A\times B$ with the product of the measures of $A$ and $B$. Passing to real values preserves this product, since the measures of the sets are finite: each is bounded by the measure of its whole probability space. This proves the stated identity.
