<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinApproximation.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity preserved by coin-tape conversion

**Claim.** For every positive slack, converting a public-coin finite-message protocol to a coin-tape protocol preserves its communication complexity.

**Proof.** The conversion pulls the original protocol back along maps that replace each coin-tape input by its associated shared-randomness outcome while leaving the private input unchanged. Pulling back changes the functions used to choose messages, but retains each message alphabet and the same continuation protocol branches. Since complexity is defined from those message-alphabet sizes and the complexities of the branches, this recursive structure gives the same complexity for the converted protocol as for the original.
