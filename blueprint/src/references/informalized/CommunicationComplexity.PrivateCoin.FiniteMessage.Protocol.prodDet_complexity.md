<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.prodDet_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Private-coin and deterministic product cost

**Claim.** The product protocol that runs a private-coin protocol and then a deterministic protocol has complexity equal to the sum of their complexities.

**Proof.** The product is a bind of the first protocol with a continuation that runs the deterministic protocol after the first output, reindexes its public inputs, and pairs its output with that first output. The bind complexity theorem for continuations of constant complexity (`Deterministic.FiniteMessage.Protocol.bind_complexity_const`) gives the first protocol's complexity plus the common continuation complexity. Reindexing inputs and mapping the output pair do not change the deterministic protocol's complexity, so that continuation complexity is exactly the complexity of the second protocol.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_complexity_const`.
