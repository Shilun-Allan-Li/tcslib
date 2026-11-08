<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.FiniteDecisionTree.orAverageQueryCost_le_auxiliaryAverageCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost of Computing OR

**Claim.** For $0<p<1$, a decision tree computing the OR-on-the-available-coordinates function has expected query cost under the biased product distribution at least $\sum_{k=0}^{|A|-1}(1-p)^k$.

**Proof.** Induct on the tree, using the biased sign law for each coordinate. If the tree is a leaf, its available set must be empty: otherwise the all-positive input makes the OR equal $1$, while changing any available coordinate to $-1$ makes it $-1$, which a constant tree cannot compute. The cost and the stated sum are then both zero. At a query of coordinate $c$, the child reached when the queried sign is $1$ computes OR on the remaining available coordinates. Indeed, fixing $c$ to $1$ removes its constraint, and the child cannot depend on that coordinate (`eval_eq_of_agreeOn`). The induction hypothesis gives that child's expected cost at least the geometric sum for $|A|-1$ coordinates. The query-cost decomposition gives total expected cost as $1$ plus the biased average of the two child costs (`auxiliaryAverageCost_query`). Under the biased law this is $(1-p)$ times the positive-child cost plus $p$ times the negative-child cost, by the two-point expectation formula (`pmfExpectation_biasedSignPMF`). The negative-child cost is nonnegative (`auxiliaryAverageCost_nonneg`), so discarding its contribution leaves at least $1+(1-p)$ times the induction bound. The geometric-sum recurrence identifies this with the required bound for $|A|$ (`orAverageQueryCost_succ`), since querying an available coordinate ensures $|A|>0$ and removing it decreases the cardinality by one.

**Key facts.** `FABL.FiniteDecisionTree.eval_eq_of_agreeOn`, `FABL.FiniteDecisionTree.auxiliaryAverageCost_query`, `FABL.pmfExpectation_biasedSignPMF`, `FABL.FiniteDecisionTree.auxiliaryAverageCost_nonneg`, `FABL.orAverageQueryCost_succ`.
