<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.averageComplexity_le_averageCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average complexity is bounded by average cost

**Claim.** For any zero-error randomized decision tree computing $g$, the average complexity of $g$ under the product distribution is at most the average cost of that tree.

**Proof.** By definition, the average complexity is the infimum of the set of average costs of zero-error randomized decision trees computing $g$. This set is bounded below by zero: every such tree has nonnegative average cost (\(\texttt{FABL.RandomizedDecisionTree.averageCost_nonneg}\)). The given tree $T$ supplies an element of the set, namely its own average cost. The infimum of a nonempty, bounded-below set is at most each of its members, so it is at most the average cost of $T$.

**Key facts.** `FABL.RandomizedDecisionTree.averageCost_nonneg`.
