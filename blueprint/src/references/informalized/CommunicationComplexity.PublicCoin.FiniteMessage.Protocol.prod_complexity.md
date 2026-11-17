<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.prod_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of a Product of Public-Coin Protocols

**Claim.** The complexity of the product of two public-coin protocols is the sum of their individual complexities.

**Proof.** Represent the public-coin protocols as deterministic protocols on input pairs of randomness and private input. Their public-coin product is the deterministic product, reindexed so that each factor receives its own randomness value and the same private input. Reindexing leaves communication complexity unchanged. The deterministic product theorem gives the sum of the two complexities (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.prod_complexity`), proving the claim.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.prod_complexity`.
