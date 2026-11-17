<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.fourierCoeff_eq_zero_of_fourierWeightAtLevel_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Weight Concentration at Level One

**Claim.** If a Boolean-valued function has Fourier weight one at level one, then every Fourier coefficient indexed by a set whose size is not one is zero.

**Proof.** Parseval for Boolean-valued functions says that the sum of the squares of all Fourier coefficients is $1$ (`sum_sq_fourierCoeff_eq_one`). The hypothesis says the portion of this sum over sets of size one is already $1$. Splitting the full sum into level one and its complement therefore leaves sum of squares zero on the complement. Each summand is nonnegative, so every square there is zero. For any $S$ with $|S|\ne1$, its square is among those terms, hence its coefficient is zero.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`.
