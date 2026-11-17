<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.matrixExponentJuntaSolverExponent_le_cutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Solver Exponent Cutoff Bound

**Claim.** For a positive rational number $\omega$ and a natural number $k$, let $c=\lceil \omega k/(\omega+1)\rceil$. Then $\omega(k-c)\le c$.

**Proof.** By the ceiling bound, the balanced exponent $\omega k/(\omega+1)$ is at most $c$. Since $\omega>0$, replacing $c$ by the smaller balanced exponent in the subtracted term can only increase the product, so $\omega(k-c)\le \omega(k-\omega k/(\omega+1))$. The expression on the right equals the balanced exponent, which is at most $c$.

**Key facts.** `FABL.matrixExponentJuntaBalancedExponent_le_cutoff`, `FABL.matrixExponentJuntaBalancedExponent_balance`.
