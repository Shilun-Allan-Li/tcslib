<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.pi_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product complexity additivity

**Claim.** The communication complexity of the product of a family of private-coin finite-message protocols is the sum of their individual complexities.

**Proof.** The private-coin product protocol is formed from the deterministic product construction by reindexing each input to pair the corresponding coin with the common public input. The deterministic product complexity theorem (`Deterministic.FiniteMessage.Protocol.pi_complexity`) says that the complexity of this product is the sum of the complexities of its factors. Reindexing inputs by the stated coordinate maps does not alter the message alphabets or protocol branches, so the private-coin definition reduces the desired equality to that theorem.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.pi_complexity`.
