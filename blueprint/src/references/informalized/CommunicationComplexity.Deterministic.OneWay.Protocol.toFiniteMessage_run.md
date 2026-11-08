<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean :: CommunicationComplexity.Deterministic.OneWay.Protocol.toFiniteMessage_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output preservation under embedding

**Claim.** Executing the finite-message protocol obtained from a one-way protocol on inputs $x$ and $y$ yields the same output as executing the one-way protocol directly.

**Proof.** The embedded protocol first selects the message sent by Alice on input $x$. Bob then encodes the value decoded from that message and his input $y$ as an index in the finite output type; the final node converts that index back to the represented output. Since the encoding and its inverse cancel, the result is exactly the one-way protocol's decoded value on the sent message and $y$.
