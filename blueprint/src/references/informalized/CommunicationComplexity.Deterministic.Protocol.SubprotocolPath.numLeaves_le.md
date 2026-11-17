<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.SubprotocolPath.numLeaves_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Count Along Subprotocol Paths

**Claim.** If there is a subprotocol path from $s$ to $p$, then $s$ has at most as many leaves as $p$.

**Proof.** Induct on the subprotocol path. A reflexive path gives equality. For a path entering an Alice node through either child, or a Bob node through either child, the induction hypothesis bounds the leaves of $s$ by those of that child. The shape of a protocol node has as its leaves the leaves of both children combined, so the selected child's leaf count is at most the node's leaf count. Transitivity of the natural-number inequality gives the desired bound in each case.
