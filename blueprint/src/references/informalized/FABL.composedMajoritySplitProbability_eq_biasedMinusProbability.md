<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.composedMajoritySplitProbability_eq_biasedMinusProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Split and Cube Probabilities

**Claim.** For every $m\ge 0$ and $p\in[0,1]$, the probability that the split composed majority of independent biased signs equals $-1$ agrees with the probability that the composed majority on the full sign cube equals $-1$ under the same law.

**Proof.** The product distribution on the full cube, when mapped through the coordinate-splitting equivalence, is exactly the split distribution (`productProbabilityPMF_map_composedMajoritySplitEquiv`). Apply the expectation-under-a-mapped-distribution identity (`pmfExpectation_map`) to the indicator that the output is $-1$. Under the splitting equivalence, the composed majority on the full cube is the split composed majority, so the two expectations—and hence the two probabilities—are equal.

**Key facts.** `FABL.productProbabilityPMF_map_composedMajoritySplitEquiv`, `FABL.pmfExpectation_map`.
