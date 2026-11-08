<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading-coordinate Fourier coefficient

**Claim.** For a Boolean function obtained by multiplying the first coordinate by the tail function $g$, the Fourier coefficient at the frequency containing coordinate $0$ and the shifted coordinates of $S$ equals the Fourier coefficient of $g$ at $S$.

**Proof.** The insertion formula for a frequency containing coordinate $0$ expresses its coefficient as half the difference between the coefficients of the two first-coordinate slices (the insertion formula, `FABL.fourierCoeff_insert_zero_tailFrequency`). At first coordinate $1$, the slice is $g$; at first coordinate $-1$, it is $-g$, since the leading coordinate multiplies the tail value. Negating a function negates each Fourier coefficient, by linearity of the finite expectation. Thus the half-difference is $(\widehat g(S)-(-\widehat g(S)))/2=\widehat g(S)$.

**Key facts.** `FABL.fourierCoeff_insert_zero_tailFrequency`, `FABL.firstCoordinateSlice_apply`, `FABL.leadingCoordinateTimes_toReal_fin_cons`.
