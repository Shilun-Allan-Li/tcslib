<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.pi_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity for Product Protocols

**Claim.** The communication complexity of the product of the public-coin protocols is the sum of the complexities of its factors.

**Proof.** View each public-coin protocol as a deterministic protocol whose inputs pair a randomness value with a private input. The deterministic product theorem says that the complexity of the product protocol on these paired input spaces is the sum of the component complexities (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.pi_complexity`). The public-coin product is obtained from that deterministic product by feeding each component its own randomness coordinate together with the same private input. This change of inputs does not alter the protocol’s communication complexity, so the deterministic theorem gives the stated sum.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.pi_complexity`.
