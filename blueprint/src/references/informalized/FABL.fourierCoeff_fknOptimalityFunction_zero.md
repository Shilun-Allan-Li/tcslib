<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fourierCoeff_fknOptimalityFunction_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Coordinate Fourier Coefficient

**Claim.** The Fourier coefficient of the associated Boolean function at the singleton frequency of the first coordinate is $1$ minus the mass of the tail upper-tail set.

**Proof.** The singleton containing the first coordinate is the frequency obtained by inserting that coordinate into the shifted empty frequency. The insertion identity (`fourierCoeff_insert_zero_tailFrequency`) writes its coefficient as half the difference of the two slice coefficients. The positive slice is the constant $1$ (`firstCoordinateSlice_fknOptimalityFunction_one`), so its empty-frequency coefficient is $1$. The negative slice is twice the set indicator minus $1$ (`firstCoordinateSlice_fknOptimalityFunction_neg_one`); its empty-frequency coefficient is $2m-1$ (`fourierCoeff_fknOptimalityLowerSlice_empty`), where $m$ is the set's mass. Thus the half-difference is $[1-(2m-1)]/2=1-m$. By definition, the delta is twice the mass, so this is $1-\mathrm{delta}/2$, as asserted.

**Key facts.** `FABL.fourierCoeff_insert_zero_tailFrequency`, `FABL.firstCoordinateSlice_fknOptimalityFunction_one`, `FABL.firstCoordinateSlice_fknOptimalityFunction_neg_one`, `FABL.fourierCoeff_fknOptimalityLowerSlice_empty`.
