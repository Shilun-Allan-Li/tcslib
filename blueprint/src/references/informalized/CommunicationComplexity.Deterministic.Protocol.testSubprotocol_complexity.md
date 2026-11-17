<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.testSubprotocol_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of the test protocol

**Claim.** The test subprotocol has complexity $2+\max(\mathrm{complexity}(q_{\mathrm{in}}),\mathrm{complexity}(q_{\mathrm{out}}))$.

**Proof.** The test protocol begins with an Alice node and then a Bob node. Each node contributes one bit of communication. After those two bits, the continuation is either $q_{\mathrm{in}}$ or $q_{\mathrm{out}}$, so its complexity is the maximum of their complexities. The recursive definition therefore gives $1+(1+\max(a,b))$, where $a$ and $b$ are the two branch complexities; this equals $2+\max(a,b)$.
