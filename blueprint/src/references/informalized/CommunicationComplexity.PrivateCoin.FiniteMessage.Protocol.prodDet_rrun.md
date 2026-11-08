<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.prodDet_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a private-coin product

**Claim.** The product of a private-coin protocol and a deterministic protocol returns the pair of their respective outputs on the same public inputs, with the first protocol using the given private coins.

**Proof.** The product is a bind of the private-coin protocol with a continuation that reindexes the deterministic protocol's inputs and maps its output to a pair with the first output. Bind execution runs that continuation on the first protocol's output (`Deterministic.FiniteMessage.Protocol.bind_run`). Reindexing execution evaluates the deterministic protocol at the public inputs (`Deterministic.FiniteMessage.Protocol.comap_run`), and mapping execution applies the pairing function to its result (`Deterministic.FiniteMessage.Protocol.map_run`). The first component is therefore the randomized output of the first protocol, and the second is the deterministic output of the second.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_run`.
