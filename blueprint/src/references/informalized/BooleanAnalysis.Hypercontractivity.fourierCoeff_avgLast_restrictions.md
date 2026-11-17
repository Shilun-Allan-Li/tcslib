<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.fourierCoeff_avgLast_restrictions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of a Last-Coordinate Average

**Claim.** The Fourier coefficient of the average of the two last-coordinate restrictions is the average of their Fourier coefficients.

**Proof.** By the definitions of the Fourier coefficient, inner product, expectation, and last-coordinate average, the left side is the uniform weight times a sum whose summand is the product of the average of the two restricted values with the character. Distribute this product across the average. Linearity of the finite sum then separates the two terms, each of which is the corresponding restricted Fourier coefficient. The remaining scalar factors give the stated average.
