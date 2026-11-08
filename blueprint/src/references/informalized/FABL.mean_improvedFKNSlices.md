<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.mean_improvedFKNSlices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Means of the Two Slices

**Claim.** If a sign-valued function on the $(n+1)$-dimensional sign cube has mean zero, then the means of its slices at first coordinate $1$ and $-1$ are respectively its first-coordinate Fourier coefficient and the negative of that coefficient.

**Proof.** Let $a$ and $b$ be the Fourier coefficients of the two slices at the empty set, corresponding to first coordinate $1$ and $-1$. The coefficient at the empty set of the full function is their average, by the tail-frequency identity (FABL.fourierCoeff_tailFrequency). Its coefficient at the singleton containing the first coordinate is half their difference (FABL.fourierCoeff_insert_zero_tailFrequency). The full function has mean zero, so its empty-set coefficient is zero (FABL.mean_eq_fourierCoeff_empty); hence $a+b=0$. The singleton coefficient is therefore $a$, and $b$ is its negative. Since each slice’s empty-set coefficient is its mean, the claimed identities follow.

**Key facts.** `FABL.fourierCoeff_tailFrequency`, `FABL.fourierCoeff_insert_zero_tailFrequency`, `FABL.improvedFKNSlice_toReal`, `FABL.mean_eq_fourierCoeff_empty`.
