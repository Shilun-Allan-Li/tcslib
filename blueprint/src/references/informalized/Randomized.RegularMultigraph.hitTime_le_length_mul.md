<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_le_length_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hitting Time Along a Walk

**Claim.** For every walk $p$ from $u$ to $v$ and every $N$, the cumulative miss probability for hitting $v$ from $u$ through step $N-1$ is at most $\operatorname{length}(p)D(|V|-1)$.

**Proof.** Proceed by induction on the walk. For the length-zero walk, the start is already the target, and the hitting time from a vertex to itself is zero. For a nonempty walk, write its first step from $u$ to $y$, followed by a walk from $y$ to $v$. The first-step relation gives adjacency in one direction or the other; symmetry of adjacency converts it to $u$ adjacent to $y$. The adjacent-vertex bound controls the cost from $u$ to $y$ by $D(|V|-1)$. Apply the induction hypothesis to the remaining walk, and use the intermediate-vertex comparison to bound the cost from $u$ to $v$ by the sum of these two costs. Since the full walk has length one more than its tail, this sum is exactly the asserted length-times bound.

**Key facts.** `Randomized.RegularMultigraph.adj_symm`, `Randomized.RegularMultigraph.hitTime_le_add`, `Randomized.RegularMultigraph.hitTime_le_of_adj`, `Randomized.RegularMultigraph.hitTime_self`.
