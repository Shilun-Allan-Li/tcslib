<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.sum_queryProbabilityOnInput_eq_inputCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total query probability equals input cost

**Claim.** For every input $x$, the sum over all coordinates of the probability that $T$ queries that coordinate on $x$ equals the expected number of queries made on $x$.

**Proof.** First interchange the finite sum over coordinates with expectation over the seed; finite sums commute with expectation ($\texttt{FABL.pmfExpectation\_sum}$). For each fixed seed, the sum over coordinates of the query indicators is the number of coordinates in the query trace, hence the tree's query count ($\texttt{FABL.FiniteDecisionTree.sum\_queryIndicator\_eq\_queryCount}$). Taking expectation over seeds therefore identifies the summed query probabilities with the expected query count, which is the input cost.

**Key facts.** `FABL.pmfExpectation_sum`, `FABL.FiniteDecisionTree.sum_queryIndicator_eq_queryCount`.
