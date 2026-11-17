<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.fourierOneNorm_reindexedSignRestriction_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm under reindexing

**Claim.** The Fourier one-norm of the reindexed restriction of the sign-valued function equals the sum of the absolute values of the restriction’s Fourier coefficients indexed by subsets of $J$.

**Proof.** Reindex the sum defining the Fourier one-norm by the bijection from coordinates in the cube of dimension $|J|$ to coordinates in $J$. This bijection also sends each finite set of coordinates to its corresponding finite subset of $J$. For each such set, the Fourier coefficient of the reindexed function equals the indexed Fourier coefficient of the restriction, by the coefficient reindexing identity (\texttt{fourierCoeff_reindexedSignRestriction}). Taking absolute values preserves this equality, so the reindexed sums agree.

**Key facts.** `FABL.fourierCoeff_reindexedSignRestriction`.
