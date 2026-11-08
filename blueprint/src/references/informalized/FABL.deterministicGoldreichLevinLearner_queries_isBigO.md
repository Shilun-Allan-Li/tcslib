<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinLearner_queries_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Query Complexity

**Claim.** The deterministic Goldreich–Levin learner's number of membership queries is asymptotically bounded by a constant multiple of the hundredth power of the task scale.

**Proof.** For each task, the learner's query count is bounded by its polynomial runtime bound (`deterministicGoldreichLevinLearner_queries_polynomial_le`). The runtime-scale factor bounds ensure the scale is at least $1$, hence nonnegative (`runtimeScale_factor_bounds`). The polynomial runtime bound is at most $2^{170}$ times the hundredth power of the task scale; combining this with the query-count bound gives the same pointwise bound for the query count. Both quantities are nonnegative, so their absolute values equal the quantities themselves. The definition of asymptotic big-O then gives the claimed result, with constant $2^{170}$.

**Key facts.** `FABL.deterministicGoldreichLevinLearner_queries_polynomial_le`, `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`.
