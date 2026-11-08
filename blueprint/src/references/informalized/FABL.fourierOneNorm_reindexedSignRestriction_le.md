<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.fourierOneNorm_reindexedSignRestriction_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm under restriction

**Claim.** For any fixed assignment outside $J$, the Fourier one-norm of the restriction to $J$ is at most the Fourier one-norm of the original sign-valued function.

**Proof.** First express the Fourier one-norm of the restriction, after reindexing its free coordinates by $J$, as the sum of the absolute values of its indexed Fourier coefficients, using the reindexing equality (\texttt{fourierOneNorm_reindexedSignRestriction_eq}). The coefficient bound for restrictions states that this sum is at most the original function’s Fourier one-norm (\texttt{sum_abs_indexedFourierCoeff_signRestriction_le_fourierOneNorm}). Combining these gives the claim.

**Key facts.** `FABL.fourierOneNorm_reindexedSignRestriction_eq`, `FABL.sum_abs_indexedFourierCoeff_signRestriction_le_fourierOneNorm`.
