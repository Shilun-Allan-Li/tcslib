<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.productLpNorm_uniformSign_eq_uniformLpNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Norm on the Sign Cube

**Claim.** The product-space $p$-norm under independent uniform signs equals the $p$-norm under the uniform distribution on the sign cube.

**Proof.** Unfold the two norm definitions. The product distribution of independent uniform signs is the uniform distribution on the sign cube (`productProbabilityPMF_uniformSign`). For a uniform probability mass function, the expectation of any function equals its uniform-cube average (`pmfExpectation_uniformPMF_eq_expect`). Applying these identities to the function $x\mapsto |f(x)|^p$ identifies the expressions inside the outer real power, and hence the norms agree.

**Key facts.** `FABL.productProbabilityPMF_uniformSign`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
