<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.fourierCoeff_tailFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient at a tail frequency

**Claim.** The Fourier coefficient at the shifted frequency is the average of the Fourier coefficients of the two slices obtained by fixing the first coordinate to $1$ and $-1$.

**Proof.** Apply the decomposition of uniform expectation on the cube according to the first coordinate (`FABL.expect_fin_cons`): the expectation is the average of the two expectations with that coordinate fixed. In either slice, the monomial at the shifted frequency reduces to the monomial at $S$ on the remaining coordinates (`FABL.monomial_tailFrequency_fin_cons`). The two resulting expectations are exactly the Fourier coefficients of the stated slices, proving the identity.

**Key facts.** `FABL.expect_fin_cons`, `FABL.monomial_tailFrequency_fin_cons`.
