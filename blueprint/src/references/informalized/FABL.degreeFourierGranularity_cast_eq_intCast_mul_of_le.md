<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.degreeFourierGranularity_cast_eq_intCast_mul_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling of Fourier Granularity

**Claim.** For natural numbers $\ell\le k$, the Fourier granularity at level $\ell$ equals $2^{k-\ell}$ times the Fourier granularity at level $k$.

**Proof.** Express both granularity values over the reals using the real-valued granularity formula (`degreeFourierGranularity_cast`). The inverse-power identity for $\ell\le k$ (`inverse_two_pow_eq_natCast_mul_inverse_two_pow`) rewrites $2^{-\ell}$ as $2^{k-\ell}2^{-k}$. Multiplying by the common factor $2$ yields the claimed scaling, with the natural-number factor viewed as an integer as in the statement.

**Key facts.** `FABL.degreeFourierGranularity_cast`, `FABL.inverse_two_pow_eq_natCast_mul_inverse_two_pow`.
