<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity under pullback

**Claim.** Pulling a protocol back along maps on its two input types preserves its communication complexity.

**Proof.** Proceed by induction on the protocol. An immediate output is unchanged by pullback, so its complexity remains zero. If Alice sends a message, pullback replaces her message function by its composition with the map on Alice's input, but the set of possible messages and the continuation protocols are unchanged except that each is itself pulled back. The induction hypothesis preserves the complexity of every continuation; consequently their supremum and the cost of Alice's message are unchanged. When Bob sends a message, the same argument applies using the map on Bob's input. Thus complexity is preserved in all cases.
