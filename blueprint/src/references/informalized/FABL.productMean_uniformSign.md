<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productMean_uniformSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Sign Mean Equals Cube Mean

**Claim.** The mean of a real-valued function on the sign cube under independent uniform signs equals its uniform mean over the sign cube.

**Proof.** The product of the uniform sign distributions is itself the uniform distribution on the sign cube (`productProbabilityPMF_uniformSign`). Substituting this identity into the definition of product mean reduces the claim to the fact that expectation under the uniform probability mass function equals the uniform mean (`pmfExpectation_uniformPMF_eq_expect`).

**Key facts.** `FABL.productProbabilityPMF_uniformSign`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
