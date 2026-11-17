<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.fourierCoeff_diffLast_restrictions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of a Last-Coordinate Half-Difference

**Claim.** The Fourier coefficient of the half-difference of the two last-coordinate restrictions is half the difference of their Fourier coefficients.

**Proof.** Expand the coefficient, inner product, expectation, and half-difference from their definitions. The summand becomes the character times the difference of the two restricted values, divided by two. Distributing the finite sum over the difference identifies the two sums with the Fourier coefficients of the restrictions; the common factor of one half gives the claimed identity.
