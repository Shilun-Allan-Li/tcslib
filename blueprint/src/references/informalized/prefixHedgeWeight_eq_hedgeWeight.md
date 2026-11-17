<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: prefixHedgeWeight_eq_hedgeWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hedge Weight Agreement

**Claim.** For row $i$ and round $t$, the prefix Hedge weight computed from the first $t$ column actions equals the Hedge weight for the induced loss sequence at time $t$.

**Proof.** Both weights are exponentials of $-\eta$ times a cumulative loss. The prefix cumulative loss equals the cumulative loss in the induced sequence through round $t$ (prefixGameLoss_eq_cumLoss). Substituting this identity into the exponents proves the weights are equal.

**Key facts.** `prefixGameLoss_eq_cumLoss`.
