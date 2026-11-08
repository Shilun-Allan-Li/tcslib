<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.RandomizedDecisionTree.averageCost_ge_sqrt_variance_mul_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance and Average Query Cost

**Claim.** For a nonconstant monotone transitive-symmetric Boolean function, a randomized decision tree whose coordinate query probabilities are equal has average cost at least the square root of the product of the function’s variance and the number of coordinates.

**Proof.** Write $\pi$ for the biased product law. If $n=0$, the variance term multiplied by $n$ is zero, and nonnegativity of average cost (`RandomizedDecisionTree.averageCost_nonneg`) proves the claim. Suppose $n>0$ and choose one coordinate $i_0$. Equal query probabilities make every coordinate’s query probability equal to that of $i_0$. Transitive symmetry and monotonicity likewise make all coordinate influences equal (`productInfluence_biased_eq_of_transitiveSymmetric_monotone`). The influence bound for decision trees (`RandomizedDecisionTree.influence_le_queryProbability`) says that the influence at $i_0$ is at most its query probability; query probabilities are nonnegative (`RandomizedDecisionTree.queryProbability_nonneg`). The OSSS inequality (`RandomizedDecisionTree.osss`) bounds the variance by the sum, over coordinates, of query probability times influence. Since each summand is the same, this gives $\operatorname{Var}_{\pi}(f)\le n q_0 I_0$, where $q_0$ and $I_0$ are the query probability and influence at $i_0$. The identity expressing average cost as the sum of coordinate query probabilities (`RandomizedDecisionTree.sum_queryProbability_eq_averageCost`) gives average cost $nq_0$. Using $I_0\le q_0$ and nonnegativity of $q_0$ yields $n\operatorname{Var}_{\pi}(f)\le (nq_0)^2$, hence the variance term under the square root is at most the squared average cost. Both quantities are nonnegative, so taking square roots proves the assertion.

**Key facts.** `FABL.RandomizedDecisionTree.averageCost_nonneg`, `FABL.productInfluence_biased_eq_of_transitiveSymmetric_monotone`, `FABL.RandomizedDecisionTree.influence_le_queryProbability`, `FABL.RandomizedDecisionTree.queryProbability_nonneg`, `FABL.RandomizedDecisionTree.osss`, `FABL.RandomizedDecisionTree.sum_queryProbability_eq_averageCost`, `FABL.pmfExpectation_nonneg`.

**Caveat.** The supplied informal statement describes a different theorem (Theorem 8.66). This account follows the formal statement and proof source, which establish a variance lower bound for randomized decision-tree average cost.
