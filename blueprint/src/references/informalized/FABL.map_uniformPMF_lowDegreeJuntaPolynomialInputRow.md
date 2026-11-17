<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.map_uniformPMF_lowDegreeJuntaPolynomialInputRow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Polynomial Input Rows

**Claim.** Applying the polynomial-input row extraction to a uniformly chosen batch of restricted assignments gives a uniform batch of sign vectors whose size is the polynomial sample count.

**Proof.** Convert every restricted assignment to its sign-vector representation using the coordinatewise equivalence between free assignments and sign vectors. The resulting batch remains uniform, since an equivalence preserves uniform finite distributions (`map_uniformPMF_equiv`). The polynomial-input extraction is then projection onto the polynomial sample indices, which form an injection into the full restricted batch. An injective-coordinate projection of a uniform function-valued batch is uniform (`map_uniformPMF_injection_projection`), giving the stated distribution.

**Key facts.** `FABL.map_uniformPMF_equiv`, `FABL.map_uniformPMF_injection_projection`.
