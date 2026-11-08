<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.fourierCoeff_firstCoordinateEvenPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Slice Fourier Coefficient

**Claim.** For every subset $S$ of the last $n$ coordinates, the Fourier coefficient of the even part of $f$ at $S$ equals the coefficient of $f$ at the corresponding shifted frequency.

**Proof.** The tail-frequency identity (`fourierCoeff_tailFrequency`) says that the coefficient of $f$ at the shifted frequency is the average of the coefficients of its two first-coordinate slices. Expand the coefficient of the even part using its definition. Pointwise, multiplying the average of the two slice values by the monomial is the average of their products with that monomial. Linearity of expectation over addition and compatibility of expectation with division by a constant then identify this coefficient with the same average of the two slice coefficients, proving the equality.

**Key facts.** `FABL.fourierCoeff_tailFrequency`.
