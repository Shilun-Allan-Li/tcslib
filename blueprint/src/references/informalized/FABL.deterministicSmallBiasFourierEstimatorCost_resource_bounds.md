<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.deterministicSmallBiasFourierEstimatorCost_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Resource Bounds

**Claim.** The estimator uses no random examples, and both its query count and its work are bounded by the polynomial budget $2^{18}Q^8$, where $Q=\text{scale}+1$ for its generator input.

**Proof.** Put $q=\text{scale}$ for the generator input, $Q=q+1$, and let $m$ be the sample count. The dimension is at most the scale, so $n\le Q$; hence $U$ has at most $Q$ elements. The sample-count bound gives $m\le4q^2\le4Q^2$. Since $Q\ge1$, these estimates also give $U.card+3\le4Q$ and $Q^3\le Q^8$. Thus the estimator's sample-dependent term satisfies $m(U.card+3)+1\le16Q^3+1\le17Q^8\le2^{17}Q^8$. The deterministic construction work is at most $2^{17}Q^8$ by the construction polynomial-budget theorem (`deterministicSmallBiasWork_le_polynomialBudget`). The work formula for the estimator (`deterministicSmallBiasFourierEstimatorCost_work`) expresses its work as construction work plus precisely the sample-dependent term above, yielding the bound $2^{18}Q^8$. For queries, the query-count formula (`deterministicSmallBiasFourierEstimatorCost_queries`) identifies the count with $m$. Since $m\le4Q^2\le4Q^8\le2^{18}Q^8$, queries meet the same budget. Finally, the random-example component is zero by `deterministicSmallBiasFourierEstimatorCost_randomExamples`.

**Key facts.** `FABL.SmallBiasFourierInput.sampleCount_le_four_mul_scale_sq`, `FABL.SmallBiasInput.n_le_scale`, `FABL.deterministicSmallBiasWork_le_polynomialBudget`, `FABL.deterministicSmallBiasFourierEstimatorCost_work`, `FABL.deterministicSmallBiasFourierEstimatorCost_queries`, `FABL.deterministicSmallBiasFourierEstimatorCost_randomExamples`.
