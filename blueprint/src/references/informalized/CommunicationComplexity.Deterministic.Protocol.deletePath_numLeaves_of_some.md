<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.deletePath_numLeaves_of_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Count After Deleting a Subprotocol Branch

**Claim.** If deletion along a path from $p$ to a subprotocol $s$ returns a protocol $q$, then $\ell(q)=\ell(p)-\ell(s)$, with truncated subtraction on the natural numbers.

**Proof.** Induct on the path, generalizing the returned protocol. In the reflexive case, deletion returns `none`, contradicting the assumption that it returns `some q`. At each of the four branching cases—Alice or Bob, and either child—the recursive deletion occurs along the chosen child while the other child is unchanged. Apply the one-branch leaf-count calculation (`deletePath_numLeaves_branch`): the rebuilt node's leaf count is the sum of its two child counts, the recursively modified child has lost exactly $\ell(s)$ leaves, and the other child is retained. This gives the original node's leaf count minus $\ell(s)$, as claimed.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.deletePath_numLeaves_branch`.
