<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.IsSubprotocol.alice_child -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alice Node Children Are Subprotocols

**Claim.** For either bit $b$, the child protocol $P(b)$ is a subprotocol of the Alice node determined by $f$ and $P$.

**Proof.** Split into the two possible values of $b$. If $b$ is false, $P(b)$ is the false child, so it is a subprotocol of the Alice node by the defining false-child rule, using reflexivity of the subprotocol relation on $P(\mathrm{false})$. If $b$ is true, the true-child rule and reflexivity give the same conclusion.
