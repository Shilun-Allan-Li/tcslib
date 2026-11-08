<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.balanced_children -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced Subprotocol Among the Children

**Claim.** Under the stated lower bound on the combined leaf counts of the two children, and the assumed balanced-subprotocol property for any child with sufficiently many leaves, the parent has a subprotocol whose leaf count multiplied by $3$ is at least $n$ and strictly less than $2n$.

**Proof.** At least one child has at least as many leaves as the other. The combined lower bound $3(L_0+L_1)\ge 2n$ then implies that this larger child has $3L_b\ge n$. If also $3L_b<2n$, that child itself is the required subprotocol of the parent. Otherwise $3L_b\ge 2n$, so the assumed property supplies a subprotocol of that child with the required bounds. Since every subprotocol of a child is a subprotocol of the parent, by transitivity of the subprotocol relation (`CommunicationComplexity.Deterministic.Protocol.IsSubprotocol.trans`), this also gives the desired subprotocol of the parent.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.IsSubprotocol.trans`.
