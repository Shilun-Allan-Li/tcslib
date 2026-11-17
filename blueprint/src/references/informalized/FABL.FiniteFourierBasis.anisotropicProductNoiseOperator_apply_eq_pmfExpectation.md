<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.anisotropicProductNoiseOperator_apply_eq_pmfExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Operator as a Kernel Expectation

**Claim.** For coordinate parameters in $[0,1]$, applying the anisotropic product noise operator to a function at an input equals the expectation of that function under the corresponding anisotropic product noise kernel.

**Proof.** By Fourier expansion (`fourier_expansion`), the function at every point is the sum of its Fourier coefficients times the corresponding product basis functions. Take expectation of this identity under the noise kernel. Linearity of expectation (`pmfExpectation_sum`) moves the finite sum outside. For each term, pull the Fourier coefficient out of the expectation (`pmfExpectation_const_mul`), then use `pmfExpectation_anisotropicProductNoiseKernel_productFunction`: the expected product basis function is its value at the input multiplied by the product of the coordinate noise parameters for its nonconstant indices. Thus each expected term is exactly the corresponding term in the definition of the anisotropic noise operator, proving the identity.

**Key facts.** `FABL.FiniteFourierBasis.fourier_expansion`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.FiniteFourierBasis.pmfExpectation_anisotropicProductNoiseKernel_productFunction`.
