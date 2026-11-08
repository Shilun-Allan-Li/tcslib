<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_le_hundred_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hitting Time from a Short Walk

**Claim.** If $D\le 100|V|$ and there is a walk from $u$ to $v$ of length at most $k$, then the cumulative miss probability for hitting $v$ from $u$ through step $N-1$ is at most $100k|V|^2$.

**Proof.** Write $n=|V|$. The walk bound gives $\operatorname{hitTime}(v,N,u)\le \operatorname{length}(p)D(n-1)$. Because the walk has initial vertex $u$, the vertex set is nonempty, so $n\ge1$ and $n-1\ge0$. The degree hypothesis then implies $D(n-1)\le100n(n-1)\le100n^2$. Combining these inequalities with $\operatorname{length}(p)\le k$ gives the claimed bound.

**Key facts.** `Randomized.RegularMultigraph.hitTime_le_length_mul`.
