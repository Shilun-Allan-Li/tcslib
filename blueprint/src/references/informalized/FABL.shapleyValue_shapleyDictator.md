<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyValue_shapleyDictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator Shapley value

**Claim.** For the game on a single player that is $1$ on coalitions containing that player and $0$ otherwise, the player's Shapley value is $1$.

**Proof.** The sum of the Shapley values over all players equals the value of the grand coalition minus the value of the empty coalition (`sum_shapleyValue`). For the dictator game on the single-player set, these coalition values are $1$ and $0$, respectively. Since there is only one player, the sum consists of that player's Shapley value, so it equals $1$.

**Key facts.** `FABL.sum_shapleyValue`.
