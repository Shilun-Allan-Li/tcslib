<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.finite_minimax_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Minimax Equality

**Claim.** For the finite zero-sum game under the stated hypotheses, the lower value equals the upper value.

**Proof.** Weak duality gives that the lower value is at most the upper value (OnlineLearning.finiteLowerValue_le_upperValue). For the reverse inequality, fix any $\varepsilon>0$. The approximate minimax theorem provides mixed strategies $p$ and $q$ such that, for every row $i$ and column $j$, the payoff of $p$ against $j$ is at least the payoff of $i$ against $q$ minus $\varepsilon$ (approx_minimax). Taking the infimum over columns shows that each payoff against $q$, less $\varepsilon$, is at most the column-infimum payoff of $p$. Taking the supremum over rows then bounds the row-supremum payoff of $q$ by that column infimum plus $\varepsilon$. The upper value is at most its value at this particular $q$, while the column-infimum payoff of $p$ is at most the lower value, since the latter is the supremum over all row strategies. Combining these inequalities gives upper value at most lower value plus $\varepsilon$. Since this holds for every positive $\varepsilon$, the upper value is at most the lower value. Together with weak duality, this proves equality. The supremum used here is bounded above because each pure-row payoff is at most $1$ (OnlineLearning.pureVsPayoff_le_one); the relevant infimum and supremum comparisons are justified by the boundedness facts for the game values (OnlineLearning.finiteUpperValue_bddBelow and OnlineLearning.finiteLowerValue_bddAbove).

**Key facts.** `OnlineLearning.finiteLowerValue_le_upperValue`, `approx_minimax`, `OnlineLearning.pureVsPayoff_le_one`, `OnlineLearning.finiteUpperValue_bddBelow`, `OnlineLearning.finiteLowerValue_bddAbove`.

**Caveat.** The supplied informal statement describes a different MW argument; this account follows the formal statement and proof source, which establish finite minimax equality by epsilon approximation.
