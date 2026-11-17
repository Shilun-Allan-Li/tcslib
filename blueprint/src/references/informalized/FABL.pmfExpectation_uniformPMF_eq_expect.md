<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_uniformPMF_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Expectation as a Finite Average

**Claim.** For a finite nonempty set, the expectation of $f$ under its uniform probability distribution equals its uniform average.

**Proof.** First identify the finite probability expectation with integration against the measure associated to the probability mass function (`pmfExpectation_eq_integral`). The integral of $f$ against the uniform distribution is its uniform average (`integral_uniformPMF_eq_expect`). Combining these identities proves the claim.

**Key facts.** `FABL.pmfExpectation_eq_integral`, `FABL.integral_uniformPMF_eq_expect`.
