<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.critical_lowerBound_le_averageComplexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Lower Bound for Average Complexity

**Claim.** For a nonconstant monotone transitive-symmetric Boolean function, its average randomized decision-tree complexity at the critical probability is at least $(n/\sigma_c)^{2/3}$.

**Proof.** The average complexity is the infimum of the average costs of randomized decision trees computing the function. This family of costs is nonempty: the complete deterministic decision tree computes the function, and hence gives one such randomized tree. The average-cost lower bound at critical probability applies to every randomized decision tree under the monotonicity, nonconstancy, and transitive-symmetry hypotheses (\texttt{RandomizedDecisionTree.averageCost_ge_critical_lowerBound}). Thus $(n/\sigma_c)^{2/3}$ is a lower bound for every member of the nonempty family, so it is at most their infimum.

**Key facts.** `FABL.FiniteDecisionTree.completeTree_computes`, `FABL.RandomizedDecisionTree.averageCost_ge_critical_lowerBound`.
