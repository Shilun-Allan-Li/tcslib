<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary simulation of finite-message protocols

**Claim.** Every deterministic finite-message protocol has a binary deterministic protocol that computes the same function on all inputs and has the same communication complexity.

**Proof.** Proceed by induction on the protocol. If it is an output node, use the same output node in the binary model; both protocols return that output and have complexity zero.

Suppose Alice sends a message from a finite nonempty set. By induction, each continuation has a binary simulation with the same outputs and complexity. The encoding lemma (`encode_alice`) combines these simulations into a binary protocol: Alice transmits an encoding of her finite-valued message, after which the matching continuation runs. The lemma ensures that this protocol computes the same output and that its complexity is the message cost, the ceiling of the base-two logarithm of the number of possible messages, plus the maximum continuation complexity. This is exactly the finite-message complexity at Alice's node.

If Bob sends the finite-valued message, apply the same encoding lemma after swapping the roles of the two parties in each inductively obtained continuation. Swapping exchanges Alice and Bob while preserving both protocol output and complexity (`swap_run` and `swap_complexity`). Swap the resulting protocol back: it now encodes Bob's message, computes the same output as the original protocol, and has the required complexity. Thus in every case there is a binary protocol with equal behavior and complexity.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.encode_alice`, `CommunicationComplexity.Deterministic.Protocol.swap_run`, `CommunicationComplexity.Deterministic.Protocol.swap_complexity`.
