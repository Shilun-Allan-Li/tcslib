<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.fourierCoeff_bonamiOddPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Part Fourier Coefficients

**Claim.** For every natural number $n$, every real-valued function $f$ on the sign cube of dimension $n+1$, and every coordinate set $S\subseteq\{1,\ldots,n\}$, the Fourier coefficient of the odd part of $f$ in its first coordinate at $S$ equals the Fourier coefficient of $f$ at the set containing the first coordinate together with the corresponding tail coordinates.

**Proof.** Apply the first-coordinate insertion formula for Fourier coefficients: the coefficient of $f$ at the set consisting of the first coordinate and the tail coordinates is the difference between the coefficients of the two slices $f(1,\cdot)$ and $f(-1,\cdot)$, divided by $2$ (`fourierCoeff_insert_zero_tailFrequency`). By definition, the odd part is the difference of those same slices divided by $2$. In the defining expectation for its Fourier coefficient, distribute multiplication by the monomial over this difference and move the constant factor $1/2$ outside the expectation. Linearity of expectation over subtraction then gives exactly the insertion formula’s right-hand side.

**Key facts.** `FABL.fourierCoeff_insert_zero_tailFrequency`.
