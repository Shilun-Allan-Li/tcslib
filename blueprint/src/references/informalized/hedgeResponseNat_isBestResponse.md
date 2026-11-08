<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: hedgeResponseNat_isBestResponse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Online Best Response

**Claim.** At each round, the online column response minimizes the payoff against the current Hedge distribution among all pure column actions.

**Proof.** Fix the round and regard the online column responses as an action sequence. The prefix Hedge mixed strategy formed from the actions before this round assigns to each row the same weight as the Hedge distribution at this round (`prefixHedgeMixedStrategy_weight_eq_hedgeDist`). By the recursive definition of the online response, the action played now is a minimizing column action (`bestColumn`) for that prefix strategy. The minimizing property of `bestColumn` (`bestColumn_spec`) says its payoff is no greater than the payoff against any column $j$. Replacing the prefix strategy’s weights by the equal Hedge weights yields the asserted inequality.

**Key facts.** `prefixHedgeMixedStrategy_weight_eq_hedgeDist`, `bestColumn_spec`.
