<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.fourierCoeff_hypercontractiveOddPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-slice Fourier coefficient

**Claim.** The Fourier coefficient of the half-difference between the two first-coordinate slices of $f$ at $S$ equals the Fourier coefficient of $f$ at the frequency formed by coordinate $0$ and the shifted copy of $S$.

**Proof.** The leading-coordinate identity (`fourierCoeff_insert_zero_tailFrequency`) expresses the coefficient of $f$ at that combined frequency as half the difference of the coefficients of its $1$ and $-1$ slices at $S$. By linearity of expectation, the Fourier coefficient of the half-difference of those slices is exactly the same half-difference. Thus the two coefficients agree.

**Key facts.** `FABL.fourierCoeff_insert_zero_tailFrequency`.
