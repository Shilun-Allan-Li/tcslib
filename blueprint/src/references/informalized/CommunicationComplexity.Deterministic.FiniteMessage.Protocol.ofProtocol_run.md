<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output preservation under embedding

**Claim.** Embedding a deterministic binary protocol as a finite-message protocol preserves its output on every input pair.

**Proof.** Proceed by induction on the protocol. If it is an output node, the embedding leaves its output value unchanged, so both executions return that value. If Alice sends a Boolean message, both executions compute the same message from Alice's input and continue with the corresponding embedded subtree; the induction hypothesis identifies that subtree's output with the original subtree's output. If Bob sends the message, the same reasoning applies using Bob's input. Hence the executions agree in every case.
