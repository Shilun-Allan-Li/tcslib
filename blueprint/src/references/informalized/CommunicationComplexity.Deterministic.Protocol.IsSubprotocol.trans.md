<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.IsSubprotocol.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Subprotocols

**Claim.** If $s$ is a subprotocol of $t$ and $t$ is a subprotocol of $u$, then $s$ is a subprotocol of $u$.

**Proof.** Induct on the derivation that $t$ is a subprotocol of $u$. In the reflexive case, $t=u$, so the given relation from $s$ to $t$ is already the desired one. In each child case, the induction hypothesis first carries the given relation from $s$ to the indicated child of $u$; applying the same false- or true-child rule then places $s$ inside the corresponding Alice or Bob node. This covers both branches for each type of node.
