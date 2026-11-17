<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.erasePath_numLeaves -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Count After Path Erasure

**Claim.** Collapsing the subtree $s$ in $p$ to one output leaf leaves $\ell(p)-\ell(s)+1$ leaves, with truncated subtraction.

**Proof.** Induct on the path from $s$ to $p$. If the path is reflexive, erasure replaces the whole protocol by one output leaf, and the formula follows because $s=p$. At a non-root step, the root has two child protocols and erasure changes only the child on the path: its leaf count $e$ is replaced by the erased count for that child, while the other child is unchanged. The induction hypothesis gives $e=\ell(P(b))-\ell(s)+1$ for the selected branch. The path's leaf-count bound (`SubprotocolPath.numLeaves_le`) ensures $\ell(s)\le\ell(P(b))$, so the truncated subtraction can be combined with the unchanged branch's leaf count to yield $\ell(P(\mathrm{false}))+\ell(P(\mathrm{true}))-\ell(s)+1$. This is precisely the claimed formula at the parent, whether the path enters Alice's or Bob's node and whichever bit it follows.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.erasePath_numLeaves_step`.
