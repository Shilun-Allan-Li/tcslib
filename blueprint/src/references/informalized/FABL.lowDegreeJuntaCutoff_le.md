<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaCutoff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Cutoff Bound

**Claim.** For every natural number $k$, the cutoff $\lfloor 3k/4\rfloor$ is at most $k$.

**Proof.** By definition the cutoff is the natural-number quotient $(3k)/4$. Since $3k\le 4k$, division by the positive number $4$ and rounding down give $(3k)/4\le k$.
