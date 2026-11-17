<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productVariance_uniformSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Sign-Cube Variance Identity

**Claim.** For every real-valued function on the sign cube, its variance under the product of uniform sign distributions equals its variance under the uniform distribution on the whole cube.

**Proof.** Unfold both variance definitions. The product of uniform sign laws is the uniform law on the entire sign cube (FABL.productProbabilityPMF_uniformSign). Expectations under a uniform probability mass function agree with the uniform average (FABL.pmfExpectation_uniformPMF_eq_expect), and the product mean agrees with the cube mean (FABL.productMean_uniformSign). Applying these identifications to the centered-square expectation yields the stated equality.

**Key facts.** `FABL.productProbabilityPMF_uniformSign`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.productMean_uniformSign`.
