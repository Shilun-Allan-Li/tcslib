<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.exists_fourierCoeff_ne_zero_of_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A nonzero Fourier coefficient

**Claim.** If a real-valued function on the sign cube is not identically zero, then at least one of its Fourier coefficients is nonzero.

**Proof.** Suppose instead that every Fourier coefficient vanishes. The Fourier expansion expresses the value of the function at each input as the sum, over all coordinate sets, of its Fourier coefficient times the corresponding monomial. Under the supposition, every summand is zero, so the function vanishes at every input. It is therefore the zero function, contradicting the hypothesis.

**Key facts.** `FABL.fourier_expansion`.
