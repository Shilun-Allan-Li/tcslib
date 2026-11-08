<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaBinaryClog_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Logarithm of a Product

**Claim.** For natural numbers $a$ and $b$, the base-two ceiling logarithm of their product is at most the sum of their base-two ceiling logarithms, including the standard convention at zero.

**Proof.** By the characterization of the ceiling logarithm, it suffices to show $ab\le 2^{\lceil\log_2 a\rceil+\lceil\log_2 b\rceil}$. The exponent law rewrites the right-hand side as $2^{\lceil\log_2 a\rceil}2^{\lceil\log_2 b\rceil}$. Each factor is at least its corresponding natural number, by the defining bound for the ceiling logarithm. Multiplying these inequalities gives the desired bound.
