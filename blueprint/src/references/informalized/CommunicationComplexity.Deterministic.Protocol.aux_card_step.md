<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.aux_card_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality Bound for a Union

**Claim.** If the natural-number cardinalities of $S_0$ and $S_1$ are at most $2^{c_0}$ and $2^{c_1}$, respectively, then the natural-number cardinality of their union is at most $2^{1+\max(c_0,c_1)}$.

**Proof.** The cardinality of a union is at most the sum of the cardinalities. Each of $2^{c_0}$ and $2^{c_1}$ is at most $2^{\max(c_0,c_1)}$, since exponentiation with base $2$ is increasing. Hence the union’s cardinality is at most $2^{\max(c_0,c_1)}+2^{\max(c_0,c_1)}=2^{1+\max(c_0,c_1)}$.
