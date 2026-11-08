<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean :: CommunicationComplexity.Deterministic.Protocol.bob_to_alice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Role Swap for a Bob-Rooted Protocol

**Claim.** A Bob-rooted protocol can be represented by a protocol with Alice and Bob’s input roles interchanged, preserving both its output on each pair of inputs and its communication complexity.

**Proof.** Take the protocol obtained by swapping the roles in the Bob-rooted protocol. The swap preserves the computation: on Alice-input $y$ and Bob-input $x$, its output equals the original protocol’s output on $x,y$ (`CommunicationComplexity.Deterministic.Protocol.swap_run`). The swap also preserves communication complexity (`CommunicationComplexity.Deterministic.Protocol.swap_complexity`). Thus this role-swapped protocol has both required properties.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.swap_run`, `CommunicationComplexity.Deterministic.Protocol.swap_complexity`.
