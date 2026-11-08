<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.deletePath_run_outside_branch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Preservation Outside a Deleted Branch

**Claim.** Under the stated branch-selection and deletion hypotheses, the protocol produced by deleting the path has the same output on $(x,y)$ as $N(P)$.

**Proof.** First substitute $P(b)=r$ and use the defining property of $N$ to reduce the desired equality to comparing the selected branch of the modified family with the corresponding branch of $P$. Split according to whether deleting the path from $r$ returns nothing or returns a protocol. If it returns nothing, `reachesPath_of_deletePath_none` says every input pair follows the path. Thus the assumption on $c$ gives $c\ne b$, so since $c$ is a bit, $c=\neg b$. The deletion equation identifies $q$ with $P(\neg b)$, and both runs therefore agree. If deletion returns $q_c$, the deletion equation identifies $q$ with $N(Q(q_c))$. When $c=b$, the selected branch of $Q(q_c)$ is $q_c$; the input cannot reach the path, by the hypothesis that a reaching input forces $c\ne b$. The induction hypothesis then identifies the run of $q_c$ with that of $r=P(b)$. When $c\ne b$, the bit property gives $c=\neg b$, and the selected branch of $Q(q_c)$ is directly $P(\neg b)$. In either case the selected run equals the corresponding branch of $P$, proving the claim.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.reachesPath_of_deletePath_none`.
