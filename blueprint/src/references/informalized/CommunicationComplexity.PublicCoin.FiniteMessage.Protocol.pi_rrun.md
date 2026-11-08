<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.pi_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Product Protocol

**Claim.** Running the product protocol with a tuple of shared randomness values returns the tuple of outputs from the individual protocols using their corresponding randomness values.

**Proof.** The public-coin execution of the product first unfolds to the deterministic execution of the product protocol on inputs whose coordinates are the corresponding randomness value paired with the common private input. Reindexing the inputs of a protocol by functions simply feeds those functions’ values into its original execution (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`). The deterministic product execution then acts componentwise: its output at each index is the execution of that factor on the corresponding input coordinates (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.pi_run`). Those coordinates are precisely the factor’s randomness value and the common private input, giving the claimed tuple.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.pi_run`.
