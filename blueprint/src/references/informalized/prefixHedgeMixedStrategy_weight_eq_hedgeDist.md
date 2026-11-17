<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: prefixHedgeMixedStrategy_weight_eq_hedgeDist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hedge Strategy Agreement

**Claim.** At round $t$, the prefix Hedge mixed strategy assigns row $i$ the same weight as the abstract Hedge distribution for the loss sequence induced by the game and column actions.

**Proof.** By definition, the prefix strategy's weight is the prefix Hedge weight divided by the prefix potential. The prefix weight equals the induced-loss Hedge weight by the equality of prefix and induced-loss weights (prefixHedgeWeight_eq_hedgeWeight); the prefix potential equals the induced-loss potential by the equality of prefix and abstract potentials (prefixPotential_eq_potential). Substituting both equalities gives precisely the Hedge distribution, whose value is its Hedge weight divided by its potential.

**Key facts.** `prefixHedgeWeight_eq_hedgeWeight`, `prefixPotential_eq_potential`.
