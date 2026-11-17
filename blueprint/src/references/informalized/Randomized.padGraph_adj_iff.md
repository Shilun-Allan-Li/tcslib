<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkPad.lean :: Randomized.padGraph_adj_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency in the padded graph

**Claim.** Two vertices of the padded graph are adjacent exactly when they are equal or related by $r$.

**Proof.** Suppose first that $u$ and $v$ are adjacent, so some edge slot at $u$ has endpoint $v$. If $u=v$, the equality alternative holds. Otherwise, the padded-neighbor characterization (`Randomized.padNbr_eq_iff`) says that this endpoint equality forces $r(u,v)$, giving the other alternative. Conversely, if $u=v$, choose the slot indexed by the natural-number value of $u$; it exists because $n\le D$, and its padded endpoint is $u$. If instead $r(u,v)$ holds, the same bound makes the slot indexed by $v$ available. When $u\ne v$, `Randomized.padNbr_eq_iff` shows that this slot has endpoint $v$. Thus either alternative supplies an adjacent edge.

**Key facts.** `Randomized.padNbr_eq_iff`.
