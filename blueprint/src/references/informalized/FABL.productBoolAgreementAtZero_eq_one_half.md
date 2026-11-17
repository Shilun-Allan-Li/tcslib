<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoise.lean :: FABL.productBoolAgreementAtZero_eq_one_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement at zero noise

**Claim.** For a uniformly distributed Boolean variable and the coordinate noise rule with retention probability zero, the probability of agreement is $1/2$.

**Proof.** Expand the inner expectation under the noise rule: the expectation of a test function is the retention probability times its value at the original point, plus the remaining probability times its uniform expectation (`pmfExpectation_productCoordinateNoisePMF`). At retention probability zero, only the uniform term remains. Expressing uniform expectation as the finite uniform average (`pmfExpectation_uniformPMF_eq_expect`), the agreement indicator is $1$ for the one matching Boolean value and $0$ for the other. Averaging over the two possible inputs therefore gives $1/2$.

**Key facts.** `FABL.pmfExpectation_productCoordinateNoisePMF`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
