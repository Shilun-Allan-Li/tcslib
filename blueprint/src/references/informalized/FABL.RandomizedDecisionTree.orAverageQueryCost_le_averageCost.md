<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.RandomizedDecisionTree.orAverageQueryCost_le_averageCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign OR Average Query Cost

**Claim.** For $0<p<1$, the average query cost of a zero-error randomized decision tree computing sign OR under independent inputs, each equal to $-1$ with probability $p$, is at least $\sum_{k=0}^{n-1}(1-p)^k$.

**Proof.** Let the input law be the specified product distribution. There is a seed whose deterministic tree has average cost under this law at most the randomized tree’s average cost (`RandomizedDecisionTree.exists_deterministic_averageCost_le`). The deterministic lower bound for OR says that any such tree computing OR has auxiliary average cost at least $\sum_{k=0}^{n-1}(1-p)^k$ (`FiniteDecisionTree.orAverageQueryCost_le_auxiliaryAverageCost`), since it computes OR on all coordinates. The auxiliary average cost equals its deterministic average query cost (`FiniteDecisionTree.auxiliaryAverageCost_complete`). Combining these inequalities for the chosen seed yields the asserted lower bound on the randomized average cost.

**Key facts.** `FABL.RandomizedDecisionTree.exists_deterministic_averageCost_le`, `FABL.FiniteDecisionTree.orAverageQueryCost_le_auxiliaryAverageCost`, `FABL.FiniteDecisionTree.auxiliaryAverageCost_complete`.
