<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.matrixExponentJuntaBalancedExponent_le_k -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced Exponent Degree Bound

**Claim.** For a positive rational matrix exponent $\omega$ and a natural number $k$, the balanced exponent is at most $k$.

**Proof.** Write the balanced exponent as $\omega k/(\omega+1)$. Since $\omega>0$, the denominator $\omega+1$ is positive, so it suffices to show $\omega k\le k(\omega+1)$. The difference between the right and left sides is $k$, which is nonnegative because $k$ is a natural number. Hence the balanced exponent is at most $k$. The positivity of $\omega+1$ is supplied by `positiveMatrixExponent_add_one_pos`.

**Key facts.** `FABL.positiveMatrixExponent_add_one_pos`.
