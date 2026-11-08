<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RestrictionMeanVariance.lean :: FABL.mean_signRestriction_eq_restrictionFourierCoeff_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean and the Empty Fourier Coefficient

**Claim.** For a fixed assignment on the complementary coordinates, the mean of the restriction of a real-valued function to the free coordinates equals the empty-set Fourier coefficient of that restriction.

**Proof.** By definition, the empty-set Fourier coefficient of a function on a sign cube is its expected value multiplied by the empty monomial. That monomial is identically one, so the coefficient equals the expectation (\(\texttt{FABL.expect_eq_indexedFourierCoeff_empty}\)). Applying this identity to the restriction gives the stated equality.

**Key facts.** `FABL.expect_eq_indexedFourierCoeff_empty`.
