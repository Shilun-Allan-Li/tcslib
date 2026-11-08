<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.boundedCubeFunction_variance_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance bound for bounded functions

**Claim.** If $f:\{\pm1\}^n\to\mathbb R$ takes values in $[-1,1]$, then its variance under the uniform distribution on the cube is at most $1$.

**Proof.** The variance has a Fourier representation as the sum of the squared Fourier coefficients over all nonempty subsets (`variance_eq_sum_sq_fourierCoeff`). Since each summand is nonnegative, this is at most the sum over all subsets. The latter sum is at most $1$ for a function taking values in $[-1,1]$ (`BoundedCubeFunction.sum_sq_fourierCoeff_le_one`).

**Key facts.** `FABL.variance_eq_sum_sq_fourierCoeff`, `FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`.
