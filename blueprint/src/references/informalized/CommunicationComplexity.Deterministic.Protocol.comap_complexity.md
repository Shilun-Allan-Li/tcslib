<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean :: CommunicationComplexity.Deterministic.Protocol.comap_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pull-Back Preserves Complexity

**Claim.** Pre-composing Alice's and Bob's message functions with maps of their input types preserves a protocol's communication complexity.

**Proof.** Proceed by structural induction on the protocol. An output protocol is unchanged by pull-back, and its complexity is zero on both sides. At an Alice node, pull-back pre-composes Alice's message function and pulls back each of the two continuation protocols. By the induction hypotheses, each continuation has the same complexity after pull-back, so their maximum, and hence the node's complexity, is unchanged. The Bob-node argument is identical, using Bob's message function.
