<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.erasePath_run_outside_branch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasure Preserves Runs Outside the Path

**Claim.** Under the stated branch-selection and run-preservation hypotheses, running $N(Q)$ on $(x,y)$ gives the same output as running $N(P)$ on $(x,y)$.

**Proof.** Use the defining property of $N$ to reduce both runs to the branches selected by $c$. If $c=b$, the selected branch of $Q$ is the erased protocol. The hypothesis that inputs following the path force $c\ne b$ therefore shows that this input does not reach the path; the induction hypothesis says the erased protocol and $r=P(b)$ have the same run. If $c\ne b$, then, because $b$ and $c$ are bits, $c=\neg b$. The selected branch of $Q$ is then the untouched branch $P(\neg b)$. In both cases the selected runs agree, which proves the equality.
