<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.sum_restrictedFourierWeight_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Weight Bound

**Claim.** For a Boolean-valued function, the sum of its restricted Fourier weights over any family of subsets of $J$ is at most $1$.

**Proof.** The family in question is a subfamily of all subsets of $J$. Each restricted Fourier weight is nonnegative, so enlarging the sum to include every subset of $J$ can only increase it (nonnegativity of restricted Fourier weights, `FABL.restrictedFourierWeight_nonneg`). The sum over all subsets of $J$ equals the sum of the squared Fourier coefficients over all frequencies (partition into restricted Fourier weights, `FABL.sum_restrictedFourierWeight_eq_sum_sq_fourierCoeff`). For a Boolean-valued function, Parseval's identity says that this total squared Fourier mass is $1$ (`FABL.sum_sq_fourierCoeff_eq_one`). Combining these facts proves the bound.

**Key facts.** `FABL.restrictedFourierWeight_nonneg`, `FABL.sum_restrictedFourierWeight_eq_sum_sq_fourierCoeff`, `FABL.sum_sq_fourierCoeff_eq_one`.
