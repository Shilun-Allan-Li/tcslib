<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.fourierCoeff_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of Fourier Coefficients

**Claim.** Multiplying a Boolean function by a real scalar multiplies each of its Fourier coefficients by that scalar.

**Proof.** Expand the Fourier coefficient as the uniform weight times the sum of the function values multiplied by the character. In each summand, associate the scalar with the function value and factor it out of the finite sum. The resulting expression is the scalar times the original Fourier coefficient.
