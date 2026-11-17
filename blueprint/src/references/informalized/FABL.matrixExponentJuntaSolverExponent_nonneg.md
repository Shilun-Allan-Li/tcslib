<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.matrixExponentJuntaSolverExponent_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Solver Exponent Nonnegativity

**Claim.** For a positive rational number $\omega$ and a natural number $k$, let $c=\lceil \omega k/(\omega+1)\rceil$. Then $0\le\omega(k-c)$.

**Proof.** The cutoff satisfies $c\le k$. Thus $k-c\ge0$, and the product of this nonnegative quantity with the positive rational number $\omega$ is nonnegative.

**Key facts.** `FABL.matrixExponentJuntaCutoff_le_k`.
