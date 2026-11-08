<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.noiseOperator_middleLayerIndicator_allOne_eq_product -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Middle-Layer Product Formula

**Claim.** At the all-ones input, the noise operator applied to the middle-layer indicator equals $\binom{2m}{m}\bigl((1+\rho)/2\bigr)^m\bigl((1-\rho)/2\bigr)^m$.

**Proof.** Express the noise operator at the all-ones input as expectation under the noise kernel (`noiseOperator_apply_eq_pmfExpectation`). In the defining sum, the indicator vanishes off the middle layer. On the middle layer, the kernel assigns every point the same probability $\bigl((1+\rho)/2\bigr)^m\bigl((1-\rho)/2\bigr)^m$ (`noiseKernel_allOne_middleLayer_mass_toReal`). Factoring this common value out leaves the sum of the indicator over all cube points, which counts the points with exactly $m$ positive coordinates. That count is $\binom{2m}{m}$ (`sum_middleLayerIndicator`), giving the formula.

**Key facts.** `FABL.noiseOperator_apply_eq_pmfExpectation`, `FABL.noiseKernel_allOne_middleLayer_mass_toReal`, `FABL.sum_middleLayerIndicator`.
