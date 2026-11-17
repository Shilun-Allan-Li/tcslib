<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.weighted_fourier_sum_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Fourier sum bound

**Claim.** For the $j$-twisted lift of any function $f$, the sum of the squared Fourier magnitudes weighted by the real parts of the Fourier coefficients is at most $1$.

**Proof.** For each frequency $s$, the real part of its Fourier coefficient is at most its modulus. Since the squared modulus is nonnegative, multiplying preserves this inequality. Parseval for the twisted lift (`ZkBLR.parseval_lift_omega_j`) says that the sum of all squared moduli is $1$. In particular, each squared modulus is at most $1$; hence multiplying it by the modulus can only decrease it. Summing these bounds gives an upper bound of $1$ by Parseval.

**Key facts.** `ZkBLR.parseval_lift_omega_j`.
