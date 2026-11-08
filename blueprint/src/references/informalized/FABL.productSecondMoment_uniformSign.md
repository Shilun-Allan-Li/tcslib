<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productSecondMoment_uniformSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment on the uniform sign cube

**Claim.** For a real-valued function on the sign cube, its second moment under the uniform product distribution equals its uniform-cube expectation of the square.

**Proof.** Unfold the definition of the second moment, so it is the PMF expectation of the function $x\mapsto f(x)^2$ under the product of $n$ uniform sign distributions. The product of these uniform coordinate laws is the uniform law on the sign cube (`productProbabilityPMF_uniformSign`). The PMF expectation under a uniform finite law equals the corresponding uniform-cube expectation (`pmfExpectation_uniformPMF_eq_expect`). Applying that identity to the square of $f$ gives the claimed equality.

**Key facts.** `FABL.productProbabilityPMF_uniformSign`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
