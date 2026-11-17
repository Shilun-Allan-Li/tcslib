<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.matrixExponentJuntaCutoff_le_k -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cutoff Degree Bound

**Claim.** For positive rational $\omega$ and natural number $k$, the cutoff $\lceil\omega k/(\omega+1)\rceil$ is at most $k$.

**Proof.** The balanced exponent is at most $k$ by `matrixExponentJuntaBalancedExponent_le_k`. Since the natural ceiling of a rational at most the natural number $k$ is at most $k$, the cutoff is at most $k as claimed.

**Key facts.** `FABL.matrixExponentJuntaBalancedExponent_le_k`.
