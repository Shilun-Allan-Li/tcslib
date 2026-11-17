<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.maximumProductInfluence_ge_variance_div_averageComplexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance versus randomized complexity

**Claim.** Under the stated full-support and orthonormal-basis assumptions, a nonconstant sign-valued function has variance divided by its randomized average complexity at most its maximum coordinate influence.

**Proof.** Write $V$ for the variance and $M$ for the maximum product influence. Full support and nonconstancy imply $V>0$. The maximum influence is nonnegative. A complete decision tree computes the function, so it supplies a randomized decision tree $T_0$ after choosing no randomness. For every randomized decision tree $T$, the variance bound gives $V\le M\,\operatorname{averageCost}(T)$. Applying this to $T_0$ shows that $M$ cannot be zero: otherwise $V\le0$, a contradiction. Thus $M>0$. Dividing the bound for arbitrary $T$ by $M$ shows that $V/M$ is a lower bound for every cost in the set whose infimum defines average complexity. That set is nonempty because it contains the cost of $T_0$. Hence $V/M$ is at most the average complexity, which is consequently positive. Rearranging this inequality gives $V/\operatorname{averageComplexity}\le M$.

**Key facts.** `FABL.productVariance_pos_of_nonconstant`, `FABL.maximumProductInfluence_nonneg`, `FABL.FiniteDecisionTree.completeTree_computes`, `FABL.RandomizedDecisionTree.variance_le_maxInfluence_mul_averageCost`.
