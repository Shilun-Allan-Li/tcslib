<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.fourierCoeff_bonamiEvenPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-Part Tail Coefficients

**Claim.** The Fourier coefficient of the even part of $f$ at $S$ equals the Fourier coefficient of $f$ at the corresponding tail-coordinate set.

**Proof.** The tail-frequency coefficient formula writes the coefficient of $f$ at the embedded set as the average of its two first-coordinate slice coefficients (FABL.fourierCoeff_tailFrequency). By definition, the even part is the pointwise average of those same slices. Multiplying that average by the monomial and taking expectation gives the average of the two slice coefficients, by linearity of expectation and factoring out the constant $1/2$. This is precisely the asserted equality.

**Key facts.** `FABL.fourierCoeff_tailFrequency`.
