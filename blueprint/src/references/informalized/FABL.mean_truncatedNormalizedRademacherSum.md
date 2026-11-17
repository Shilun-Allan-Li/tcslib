<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.mean_truncatedNormalizedRademacherSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Truncated Sign Sum

**Claim.** For every nonnegative integer $n$, the mean on the sign cube of the truncation to $[-1,1]$ of the normalized Rademacher sum with all coefficients equal to $1/\sqrt n$ is zero.

**Proof.** Negating every coordinate is a bijection of the sign cube, so reindexing the mean by this map does not change it. The truncated normalized sum changes sign under this negation (`FABL.truncatedNormalizedRademacherSum_neg`). Consequently, the same mean is also the mean of the negative of the original function, which is the negative of the original mean. A real number equal to its negative is zero, proving the claim.

**Key facts.** `FABL.truncatedNormalizedRademacherSum_neg`.
