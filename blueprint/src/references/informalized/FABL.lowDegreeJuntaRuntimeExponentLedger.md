<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaRuntimeExponentLedger -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Junta runtime exponent inequalities

**Claim.** For every $k$, with $q=\lfloor 3k/4\rfloor$ and $\ell=k-q$, one has $q\le q+3$ and $3\ell\le q+3$.

**Proof.** The first inequality follows because adding $3$ to a natural number cannot make it smaller. For the second, apply the established bound $3\ell\le q+3$ for the low-degree polynomial degree (Lean name: `three_mul_lowDegreeJuntaPolynomialDegree_le_cutoff_add_three`). Unfolding the definitions identifies that degree with $\ell$ and the cutoff with $q$, yielding the result.

**Key facts.** `FABL.three_mul_lowDegreeJuntaPolynomialDegree_le_cutoff_add_three`.
