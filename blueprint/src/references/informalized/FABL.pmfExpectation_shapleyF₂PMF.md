<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.pmfExpectation_shapleyF₂PMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Under the Shapley Cube Distribution

**Claim.** The expectation of $f$ under the Shapley cube distribution equals the expectation under the corresponding subset distribution of $f$ evaluated at each subset's indicator vector.

**Proof.** The cube distribution is the image of the subset distribution under the inverse of the support correspondence. The expectation-under-mapping identity (`pmfExpectation_map`) therefore rewrites the expectation on the cube as the subset expectation of $f$ composed with that map. By the definition of the Shapley expectation, this is exactly the claimed expression.

**Key facts.** `FABL.pmfExpectation_map`.
