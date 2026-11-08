<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyValue_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of the Shapley value

**Claim.** The Shapley value of a finite pointwise sum of games, at a given player, equals the sum of their Shapley values at that player.

**Proof.** At every coalition $S$, the marginal contribution of the pointwise sum is the sum of the individual marginal contributions: evaluation distributes over the finite sum, and subtraction distributes across it. Taking expectation over coalitions preserves finite sums (`pmfExpectation_sum`), which gives the asserted identity.

**Key facts.** `FABL.pmfExpectation_sum`.
