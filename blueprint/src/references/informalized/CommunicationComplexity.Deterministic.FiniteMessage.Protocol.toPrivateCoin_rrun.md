<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Private coins do not change deterministic output

**Claim.** The private-coin protocol obtained by discarding both players' coins returns the deterministic protocol's output for every input pair and every pair of coin draws.

**Proof.** By definition, a private-coin execution evaluates the reindexed protocol on the paired coin and input values. The input-reindexing execution rule says this is the original protocol run on the images of those pairs under the projections to the input components (`comap_run`). Those images are exactly the original inputs, so the result is the deterministic protocol's output, independently of the coin draws.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`.
