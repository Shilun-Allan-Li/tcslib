<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_eq_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation as an integral

**Claim.** For a finite measurable space in which every singleton is measurable, the expectation of a real function under a probability mass function equals its integral against the measure induced by that mass function.

**Proof.** The integral of a function on a finite space with respect to the measure induced by a probability mass function is the finite sum of its values weighted by the masses of the individual points. Applying this finite-sum formula, the integral becomes the defining sum for the expectation: each mass is viewed as a real number, and multiplication agrees with scalar multiplication. Thus the two quantities are equal.
