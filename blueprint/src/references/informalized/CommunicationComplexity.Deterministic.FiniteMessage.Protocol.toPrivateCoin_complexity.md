<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity under private-coin extension

**Claim.** Replacing a deterministic protocol's input types by private-coin and input pairs while having each message ignore the coin preserves communication complexity.

**Proof.** The private-coin protocol is defined by reindexing each player's inputs to their underlying input component. Reindexing changes the message functions' domains but leaves their message alphabets and continuation trees unchanged. The complexity calculation depends on those alphabets and continuation complexities, so it is unchanged; unfolding the reindexing definition establishes the equality.
