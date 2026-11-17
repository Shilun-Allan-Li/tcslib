<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.prod_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Product of Public-Coin Protocols

**Claim.** The product protocol, on any pair of private inputs and any pair of shared randomness values, returns the pair of outputs from the two protocols using their respective randomness values.

**Proof.** The randomized execution of the public-coin product is the deterministic execution after each side’s input has been reindexed to give the first protocol its first randomness value and the second protocol its second randomness value. Reindexing transfers execution to those specified inputs (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`). The deterministic product execution returns the pair of executions on the two input coordinates (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.prod_run`). Substituting the reindexed coordinates yields the asserted pair.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.prod_run`.
