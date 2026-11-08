<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.rbind_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of Fresh-Randomness Bind

**Claim.** Running the fresh-randomness bind on a pair of coin pairs runs $p$ using the first coordinates, then runs the continuation selected by its output using the second coordinates.

**Proof.** Unfold the definition of fresh-randomness execution: it runs the underlying deterministic protocol on each party’s coin-input pair. The deterministic bind execution theorem identifies the run of a bind with running the original protocol, then running the continuation selected by that output (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`). The deterministic change-of-input theorem says that running a reindexed protocol is the same as running the original protocol on the reindexed inputs (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`). For the first stage those maps retain the first coin coordinates; for the continuation they retain the second. Substituting these identities gives the asserted execution formula.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`.
