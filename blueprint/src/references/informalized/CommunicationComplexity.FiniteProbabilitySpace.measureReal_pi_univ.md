<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.measureReal_pi_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product measure of a box

**Claim.** For a finite family of finite probability spaces, the product measure of a box factors as the product of the measures of its coordinate sets.

**Proof.** The measure on the finite product is the product measure of the coordinate measures. The product-measure formula for measurable boxes identifies the measure of the box with the product of the coordinate measures of the sets. All coordinate sets are measurable by discreteness. Converting from nonnegative extended-real values to real values preserves this finite product: each factor is finite because it is at most the probability of its whole space. This gives the stated factorization.
