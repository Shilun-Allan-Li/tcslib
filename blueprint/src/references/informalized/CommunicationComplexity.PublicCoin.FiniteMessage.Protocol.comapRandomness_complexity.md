<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.comapRandomness_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity under randomness reindexing

**Claim.** Precomposing the shared randomness in every message function with any map $h\colon\Omega'\to\Omega$ leaves the protocol’s communication complexity unchanged.

**Proof.** The reindexing replaces each message function by its composite with the corresponding map on the player’s input, while leaving the protocol’s branching structure intact. Complexity is determined recursively by that structure: the message alphabet’s contribution and the maximum complexity among the continuation branches. Thus each constructor contributes exactly the same amount before and after reindexing, giving equality of complexities.
