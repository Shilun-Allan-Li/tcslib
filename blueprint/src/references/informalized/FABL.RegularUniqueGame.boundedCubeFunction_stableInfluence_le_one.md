<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.boundedCubeFunction_stableInfluence_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable influence bound

**Claim.** For a function $f:\{\pm1\}^n\to\mathbb R$ taking values in $[-1,1]$, a parameter $0\le\rho\le1$, and a coordinate $i\in[n]$, the stable influence of $f$ at $i$ is at most $1$.

**Proof.** Since $0\le\rho\le1$, every power $\rho^{|S|-1}$ appearing for a set $S$ containing $i$ is at most $1$. Each squared Fourier coefficient is nonnegative, so term by term the stable influence is at most the sum of the squared Fourier coefficients over sets containing $i$. Enlarging this index set to all subsets can only increase the sum, again because the summands are nonnegative. The total sum of squared Fourier coefficients is at most $1$ for a function taking values in $[-1,1]$ (`BoundedCubeFunction.sum_sq_fourierCoeff_le_one`), giving the result.

**Key facts.** `FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`.
