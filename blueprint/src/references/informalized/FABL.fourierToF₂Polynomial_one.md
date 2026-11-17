<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.fourierToF₂Polynomial_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transform of the constant one function

**Claim.** Applying the Fourier-to-bit transformation to the constant-one function on the sign cube gives the identically zero function on the bit cube.

**Proof.** At any bit-cube input, the corresponding sign-cube input is evaluated by the constant-one function, so the transformed value is $(1-1)/2=0$. Since this holds at every input, the transformed function is identically zero.
