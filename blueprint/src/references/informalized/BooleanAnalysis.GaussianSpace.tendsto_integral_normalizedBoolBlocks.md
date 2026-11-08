<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedBlocks.lean :: BooleanAnalysis.GaussianSpace.tendsto_integral_normalizedBoolBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian limit for normalized Boolean blocks

**Claim.** For a bounded continuous function on $\mathbb R^n$, its expectation at the vector of normalized independent Boolean sign sums converges to its integral under standard Gaussian measure.

**Proof.** Fix $m$ and let $f$ send a block of $m+1$ Boolean signs to its normalized signed sum. Mapping the uniform product measure on each block through $f$ gives the normalized Boolean sum law. Applying the same map coordinatewise sends the product of the block measures to the product of these one-dimensional laws, by the product-measure mapping identity. Since $F$ is continuous, its integral against the mapped measure equals the integral of its composition with the map against the original Boolean product measure. Thus the expectation in the claim equals the integral of $F$ against the product normalized-sum law. That integral converges to the Gaussian integral by the product normalized-sum convergence theorem (tendsto_integral_normalizedBoolSum_pi).

**Key facts.** `BooleanAnalysis.GaussianSpace.tendsto_integral_normalizedBoolSum_pi`.
