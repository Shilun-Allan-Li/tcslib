<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.deletePath_numLeaves_branch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Count After Path Deletion

**Claim.** In the stated branch construction, the resulting protocol has leaf count equal to the leaf count of the parent node minus the leaf count of the deleted subprotocol.

**Proof.** First identify the continuing branch $P(b)$ with the protocol $r$. The parent constructor has leaf count equal to the sum of its two child counts. Split according to the recursive deletion result. If it is `none`, the deletion at this stage leaves just the untouched sibling $P(!b)$. The fact that a path whose deletion is `none` identifies the subprotocol with its endpoint (`eq_of_deletePath_none`), together with the branch identification, makes the claimed subtraction equality a direct leaf-count calculation. If recursive deletion returns $q_c$, the induction hypothesis gives its leaf count as $\ell(P(b))-\ell(s)$. The rebuilt parent retains this modified child and the untouched sibling; adding their leaf counts and using the two branch identities gives the parent leaf count minus $\ell(s)$. The fact that a subprotocol's leaf count is at most its containing protocol's (`SubprotocolPath.numLeaves_le`) justifies the natural-number subtraction calculation.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.eq_of_deletePath_none`, `CommunicationComplexity.Deterministic.Protocol.SubprotocolPath.numLeaves_le`.
