<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.finiteUpperValue_bddBelow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for the Upper Value

**Claim.** For a game with at least one row action, the set of row-supremum values over mixed column strategies is bounded below.

**Proof.** Fix any mixed column strategy $q$. Every pure-row payoff against $q$ is nonnegative, by the payoff nonnegativity and the strategy weights, so in particular the supremum over rows is at least one such payoff and hence at least zero. This supremum is well-defined as a real supremum: each pure-row payoff is at most $1$, so the set of these payoffs is bounded above. Thus zero is a lower bound for the row-supremum value for every $q$, and consequently for the set of all such values.

**Key facts.** `OnlineLearning.pureVsPayoff_le_one`, `OnlineLearning.pureVsPayoff_nonneg`.
