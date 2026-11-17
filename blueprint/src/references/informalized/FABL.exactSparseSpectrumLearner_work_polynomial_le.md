<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumLearner_work_polynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Work Bound

**Claim.** For every Boolean target function on the $n$-dimensional sign cube and every natural number $k$, the local work charged when the exact sparse-spectrum learner is run against the target is at most $1+2^{171}\bigl(12(n+1)(2^k+1)^2\bigr)^{100}$.

**Proof.** The resource bound for the exact sparse-spectrum learner shows that its natural-number work cost is at most the specified work budget (the work component of `exactSparseSpectrumLearner_resource_bounds`). Viewing this inequality over the reals preserves its order. The work budget is itself at most the polynomial runtime bound, by `exactSparseSpectrumWorkBudget_cast_le_polynomialRuntimeBound`. Transitivity gives the claimed bound.

**Key facts.** `FABL.exactSparseSpectrumLearner_resource_bounds`, `FABL.exactSparseSpectrumWorkBudget_cast_le_polynomialRuntimeBound`.
