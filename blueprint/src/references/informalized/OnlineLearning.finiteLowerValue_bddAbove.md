<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.finiteLowerValue_bddAbove -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the finite lower value

**Claim.** For every mixed row strategy, its least payoff against a pure column is at most $1$, so the set of finite lower values is bounded above by $1$.

**Proof.** Fix a mixed row strategy $p$. Nonnegativity of the matrix entries and of the strategy weights makes every expected payoff against a pure column nonnegative, so the infimum over columns is well-defined as a real lower-bounded infimum. Choose any column, which exists because the column set is nonempty. The infimum is at most the payoff against that column, and every such expected payoff is at most $1$ (OnlineLearning.payoffVsPure_le_one). Therefore the infimum is at most $1$ for every $p$, proving the asserted uniform upper bound. The nonnegativity fact used for the lower bound is OnlineLearning.payoffVsPure_nonneg.

**Key facts.** `OnlineLearning.payoffVsPure_nonneg`, `OnlineLearning.payoffVsPure_le_one`.
