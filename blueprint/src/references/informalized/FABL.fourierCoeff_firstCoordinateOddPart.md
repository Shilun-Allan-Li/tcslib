<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.fourierCoeff_firstCoordinateOddPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Slice Fourier Coefficient

**Claim.** For every subset $S$ of the last $n$ coordinates, the Fourier coefficient of the odd part of $f$ at $S$ equals the coefficient of $f$ at the frequency consisting of the first coordinate together with the shifted copy of $S$.

**Proof.** The insertion identity (`fourierCoeff_insert_zero_tailFrequency`) expresses the coefficient at the frequency containing the first coordinate as half the difference between the coefficients of the two first-coordinate slices. Expand the coefficient of the odd part from its definition. Pointwise, multiplying the half-difference of the slice values by the monomial gives half the difference of their products with that monomial. Linearity of expectation over subtraction and compatibility with division by a constant show that this is precisely the half-difference of the slice coefficients, as required.

**Key facts.** `FABL.fourierCoeff_insert_zero_tailFrequency`.
