<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.iIndepFun_coordIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of Coordinate Indicators

**Claim.** Under the product measure on Boolean strings of length $k$ with Bernoulli-$p$ coordinate laws, the coordinate indicators are mutually independent.

**Proof.** The measure is a product over the coordinates, and each coordinate indicator is the function of the corresponding Boolean coordinate that sends `true` to $1$ and `false` to $0$. The product-measure independence theorem says that measurable functions applied separately to the coordinates remain mutually independent. Each of these two-valued functions is measurable on the discrete Boolean space, so that theorem gives the desired independence.
