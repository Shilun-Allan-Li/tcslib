<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.comapRandomness_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity Under Randomness Reindexing

**Claim.** Reindexing a private-coin protocol's randomness through arbitrary maps preserves its worst-case communication complexity.

**Proof.** The reindexed protocol is obtained by applying the deterministic protocol's input reindexing to Alice's and Bob's paired inputs: the maps send $(\omega_x',x)$ to $(hX(\omega_x'),x)$ and $(\omega_y',y)$ to $(hY(\omega_y'),y)$. Reindexing inputs changes the functions used to choose messages, but leaves the message alphabets and all subsequent protocol branches unchanged. Since complexity is determined recursively by those message alphabet sizes and the maximum complexity among branches, the deterministic reindexing result gives the same complexity. The private-coin theorem follows by unfolding the reindexing abbreviation.
