<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaCutoff_le_three_mul_polynomialDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cutoff and Degree Bound

**Claim.** For every natural number $k$, if $r=\lfloor3k/4\rfloor$ and $d=k-r$, then $r\le3d$.

**Proof.** By the definitions, the desired inequality is $3k/4\le 3(k-3k/4)$, with both divisions interpreted as natural-number division. Clearing the denominator reduces this to an elementary inequality between natural numbers; the quotient and remainder properties of division by $4$ verify it, including when $k$ is not divisible by $4$.
