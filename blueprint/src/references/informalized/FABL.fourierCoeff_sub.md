<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.fourierCoeff_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtraction of Fourier coefficients

**Claim.** For real-valued functions on the Boolean cube, the Fourier coefficient of their difference at any coordinate set is the difference of their Fourier coefficients.

**Proof.** Expand the integrand in the definition of the Fourier coefficient: pointwise, $(f(x)-g(x))\chi_S(x)=f(x)\chi_S(x)-g(x)\chi_S(x)$. The uniform expectation on the finite cube distributes over subtraction, so taking expectations gives the asserted identity.
