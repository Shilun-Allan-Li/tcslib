<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.IsSubprotocol.bob_child -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bob Node Children Are Subprotocols

**Claim.** For either bit $b$, the child protocol $P(b)$ is a subprotocol of the Bob node determined by $f$ and $P$.

**Proof.** Split into the two possible values of $b$. If $b$ is false, reflexivity makes the false child a subprotocol of itself, and the false-child rule then makes it a subprotocol of the Bob node. If $b$ is true, use reflexivity on the true child followed by the true-child rule.
