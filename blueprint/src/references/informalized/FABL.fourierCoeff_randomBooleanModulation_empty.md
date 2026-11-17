<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.fourierCoeff_randomBooleanModulation_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Modulation shifts a Fourier coefficient

**Claim.** Multiplying a Boolean function pointwise by the parity character on $S$ makes its Fourier coefficient at the empty set equal to the original function’s Fourier coefficient at $S$.

**Proof.** Expand both Fourier coefficients as expectations. At each input $x$, the modulated function has value $f(x)\chi_S(x)$, by multiplicativity of the sign value and the identity that the sign value of the parity character is the monomial on $S$ (\(\texttt{FABL.signValue_randomBooleanParitySign}\)). The empty-set monomial is $1$, so the integrand on the modulated side is exactly $f(x)\chi_S(x)$, which is the integrand for the coefficient of $f$ at $S$. The expectations, and hence the coefficients, are equal.

**Key facts.** `FABL.signValue_randomBooleanParitySign`.
