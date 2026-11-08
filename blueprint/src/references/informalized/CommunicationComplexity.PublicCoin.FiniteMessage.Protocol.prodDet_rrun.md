<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.prodDet_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution with a Deterministic Product Factor

**Claim.** The product of a public-coin protocol and a deterministic protocol outputs the pair consisting of their respective executions on the given inputs and shared randomness.

**Proof.** Unfold the product as a bind: first execute the public-coin protocol, then run a reindexed copy of the deterministic protocol and pair its output with the first result. Execution of a bind is execution of the first protocol followed by execution of the selected continuation (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`). The reindexing feeds the original private inputs to the deterministic protocol and hence leaves its execution at those inputs (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`). Mapping the continuation’s output to a pair therefore gives the public-coin output together with the deterministic output, as claimed.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_run`.
