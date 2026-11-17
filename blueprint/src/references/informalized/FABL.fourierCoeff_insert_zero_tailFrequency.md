<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.fourierCoeff_insert_zero_tailFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading-coordinate Fourier coefficient

**Claim.** The Fourier coefficient at the frequency consisting of coordinate $0$ and the shifted coordinates of $S$ is half the difference between the two slice coefficients at $S$.

**Proof.** Split the uniform expectation over the first coordinate into the average of its two slices (`expect_fin_cons`). On either slice, the monomial at the combined frequency factors as the first coordinate's sign times the monomial at $S$ (`monomial_insert_zero_tailFrequency_fin_cons`). The sign is $1$ on the positive slice and $-1$ on the negative slice (`signValue_one`, `signValue_neg_one`). Thus the two slice expectations enter with opposite signs, and their average is half their difference.

**Key facts.** `FABL.expect_fin_cons`, `FABL.monomial_insert_zero_tailFrequency_fin_cons`, `FABL.signValue_one`, `FABL.signValue_neg_one`.
