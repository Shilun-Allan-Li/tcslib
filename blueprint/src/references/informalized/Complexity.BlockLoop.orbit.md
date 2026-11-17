<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit of a block countdown

**Claim.** For each $i\le K$, the $i$-th iterate of the block-loop step at $s_0$ is the encoding of $P(i)$, the remaining countdown $1^{K-i}$, and $Q(i)$.

**Proof.** We argue by induction on $i$, after replacing the assumed description of the step and the initial state by their definitions. At $i=0$, the iterate is the initial state, and the asserted formula is exactly its given encoding. For the induction step, suppose $i+1\le K$. Then $i<K$, so $P(i)$ is nonempty and the update hypotheses apply. The inner countdown has length $K-i=(K-(i+1))+1$: its first true bit is removed by the step, leaving exactly $1^{K-(i+1)}$. Because the head is nonempty and this countdown is nonempty, the step takes its active branch; it replaces the head by $\mathrm{upd}(P(i),Q(i))=P(i+1)$ and the next state by $\mathrm{nxt}(P(i),Q(i))=Q(i+1)$. The resulting encoding is therefore the claimed one for $i+1$.
