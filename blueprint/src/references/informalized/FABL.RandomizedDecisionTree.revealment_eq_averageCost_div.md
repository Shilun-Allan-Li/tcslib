<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.revealment_eq_averageCost_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Revealment under equal query probabilities

**Claim.** If $n>0$ and every coordinate has the same query probability under independent inputs of law $\pi$, then the revealment of $T$ equals its average number of queries divided by $n$.

**Proof.** Choose a coordinate $i_0$ (for instance, the coordinate indexed by $0$), which exists since $n>0$. All coordinates have the same query probability as $i_0$, so the supremum defining revealment equals that common value. The sum of the query probabilities over all coordinates equals the average cost ($\texttt{FABL.RandomizedDecisionTree.sum\_queryProbability\_eq\_averageCost}$). By equality of the coordinate probabilities, this sum is $n$ times the query probability of $i_0$. Thus the average cost is $n$ times the revealment, and division by the positive integer $n$ gives the stated identity.

**Key facts.** `FABL.RandomizedDecisionTree.sum_queryProbability_eq_averageCost`.
