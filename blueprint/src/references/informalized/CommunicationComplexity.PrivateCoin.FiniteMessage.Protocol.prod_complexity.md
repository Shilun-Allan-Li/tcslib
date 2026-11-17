<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.prod_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product protocol complexity

**Claim.** The complexity of the product of two private-coin finite-message protocols, using paired private randomness, is the sum of their complexities.

**Proof.** The private-coin product is the deterministic product of the two protocols followed by a reindexing of inputs that supplies each factor its own coin together with the shared public input. The deterministic product complexity theorem (`Deterministic.FiniteMessage.Protocol.prod_complexity`) gives the sum of the factors' complexities. Reindexing the inputs does not change the message alphabets or branches, and hence leaves complexity unchanged; the claimed equality follows.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.prod_complexity`.
