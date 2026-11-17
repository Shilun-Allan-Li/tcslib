<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.triple_expectation_eq_cube_fourier_aux_h_substitute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation after Fourier substitution

**Claim.** If the convolution of the sign lift with itself has the stated Fourier expansion, then the expectation of the sign lift times that convolution equals the sum of squared Fourier coefficients weighted by the sign lift’s character correlations.

**Proof.** Substitute the assumed expansion of the convolution into the expectation. Distribute multiplication by the sign lift over the finite sum, then interchange the finite sum over subsets with the finite uniform average over inputs. Pull each coefficient, which is independent of the input, outside its expectation. The resulting expression is precisely the claimed sum.
