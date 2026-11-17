<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.prodDet_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of a Product with a Deterministic Protocol

**Claim.** The product of a public-coin protocol and a deterministic protocol has complexity equal to the sum of their complexities.

**Proof.** The product is formed by running the public-coin protocol first and then binding its output to a continuation that runs the deterministic protocol on the private inputs. Reindexing the deterministic protocol’s inputs to ignore the randomness coordinate, and pairing its output with the first protocol’s output, do not change its complexity. Thus every continuation has the same complexity as the deterministic protocol. The constant-continuation bind theorem states that binding a protocol to continuations all of complexity $c$ adds exactly $c$ to its complexity (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_complexity_const`). Taking $c$ to be the complexity of the deterministic protocol gives the result.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_complexity_const`.
