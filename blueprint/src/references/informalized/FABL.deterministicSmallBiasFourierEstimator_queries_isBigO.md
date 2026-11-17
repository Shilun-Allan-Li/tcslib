<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.deterministicSmallBiasFourierEstimator_queries_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic Query Bound

**Claim.** As the scale of small-bias Fourier estimation tasks tends to infinity, the estimator's query count is $O((\text{scale}+1)^8)$.

**Proof.** The resource-bounds proposition (`deterministicSmallBiasFourierEstimatorCost_resource_bounds`) gives, for every task, a query count at most its polynomial budget $2^{18}(\text{scale}+1)^8$. Regard the natural-number quantities as real numbers; the same inequality holds after casting, and absolute values of these nonnegative quantities equal the quantities themselves. Thus the query function is bounded by the constant $2^{18}$ times the comparison function at every task. The bounded form of the definition of big-O therefore yields the claimed asymptotic estimate along tasks whose scale tends to infinity.

**Key facts.** `FABL.deterministicSmallBiasFourierEstimatorCost_resource_bounds`.
