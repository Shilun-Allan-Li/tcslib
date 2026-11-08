<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.fourierCoeff_hypercontractiveEvenPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Slice Fourier Coefficient

**Claim.** The Fourier coefficient of the average of the two first-coordinate slices of $f$ at $S$ equals the coefficient of $f$ at the frequency obtained by shifting every index in $S$ up by one.

**Proof.** The tail-frequency identity (`fourierCoeff_tailFrequency`) states directly that the coefficient at the shifted frequency is the average of the coefficients of the two slices. Expanding the coefficient of the averaged function, distribute multiplication by the monomial across the average: pointwise this is the average of the two slice values multiplied by that monomial. Linearity of expectation and compatibility with division by a constant show that its coefficient is the same average of the slice coefficients. Hence it equals the coefficient at the shifted frequency.

**Key facts.** `FABL.fourierCoeff_tailFrequency`.
