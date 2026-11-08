<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumLearner_queries_polynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Query Bound

**Claim.** For every Boolean target and every $k$, the exact sparse spectrum learner’s number of membership queries is at most the polynomial runtime bound for $(n,k)$.

**Proof.** The exact sparse spectrum learner’s resource bound theorem says that its query count is at most the exact sparse spectrum query budget (`exactSparseSpectrumLearner_resource_bounds`). Casting this natural-number inequality to the reals preserves the order. The query budget is itself at most the stated polynomial runtime bound (`exactSparseSpectrumQueryBudget_cast_le_polynomialRuntimeBound`). Transitivity gives the required inequality.

**Key facts.** `FABL.exactSparseSpectrumLearner_resource_bounds`, `FABL.exactSparseSpectrumQueryBudget_cast_le_polynomialRuntimeBound`.
