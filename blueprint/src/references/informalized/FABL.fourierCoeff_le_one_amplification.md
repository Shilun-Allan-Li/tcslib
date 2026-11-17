<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.fourierCoeff_le_one_amplification -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient upper bound

**Claim.** For a sign-valued function $f$, every Fourier coefficient is at most $1$.

**Proof.** The square of the coefficient at $S$ is one nonnegative term in the sum of the squares of all Fourier coefficients, so it is at most that sum. Parseval's identity for a sign-valued function (`sum_sq_fourierCoeff_eq_one`) says that the sum is $1$. Thus the coefficient's square is at most $1$, which implies that the coefficient itself is at most $1$.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`.
