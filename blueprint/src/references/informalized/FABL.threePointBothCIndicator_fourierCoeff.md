<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.threePointBothCIndicator_fourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Indicator Fourier Coefficient

**Claim.** For any pair of Fourier indices, the coefficient of the two-coordinate indicator $g(x_0)g(x_1)$ is the product of the corresponding one-coordinate coefficients of $g$.

**Proof.** The two-coordinate Fourier coefficient is the expectation of the indicator times the product-basis function. Pointwise, this integrand factors as the product over the two coordinates of $g(x_i)\phi_{a_i}(x_i)$. Expectation under the independent product of the uniform three-point distributions factors into the product of the one-coordinate expectations ( `pmfExpectation_independentProductPMF_prod`). Each factor is the corresponding coefficient of $g$ ( `threePointCIndicator_coefficient`), so the coefficient is their product.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.threePointCIndicator_coefficient`.
