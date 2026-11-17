<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/OneWayMinimax.lean :: CommunicationComplexity.PublicCoin.OneWay.Protocol.toDeterministic_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost invariant under fixing randomness

**Claim.** Fixing a public-randomness outcome in a one-way protocol preserves its communication cost, namely the bit cost determined by the size of its shared message codebook.

**Proof.** Fixing $\omega$ changes the encoder and decoder by evaluating them on inputs that include this fixed outcome. The message codebook itself is unchanged. Since the cost is the ceiling of the base-two logarithm of the codebook size, the two costs are equal by their definitions.
