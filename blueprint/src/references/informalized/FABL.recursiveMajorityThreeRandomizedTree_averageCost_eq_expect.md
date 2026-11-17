<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeRandomizedTree_averageCost_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform-input average cost

**Claim.** For every depth $d$, the randomized recursive three-way majority tree’s average query cost under uniform sign inputs equals the expected value of its input cost on a uniformly chosen sign vector of length $3^d$.

**Proof.** Unfolding average cost identifies it with the expectation under the product distribution of the input coordinates. The product of uniform sign distributions is itself the uniform distribution on the sign cube, by the product-uniformity fact (`productProbabilityPMF_uniformSign`). The uniform PMF expectation agrees with the cube expectation (`pmfExpectation_uniformPMF_eq_expect`), giving the asserted equality.

**Key facts.** `FABL.productProbabilityPMF_uniformSign`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
