<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Cumulative Miss Probability

**Claim.** For a finite regular multigraph of positive degree, if $t$ is reachable from $s$ by a finite adjacency walk, then for every $N$ the cumulative miss probability through step $N-1$ is at most $2D|V|^3$.

**Proof.** Let $C(u)$ mean that $u$ can reach $t$, and define $F(u)$ to be the cumulative miss probability from $u$ when $C(u)$ holds, and zero otherwise. Hit-time nonnegativity (`hitTime_nonneg`) gives $F(u)\ge 0$. Moreover, if $C(u)$ holds, then every neighbor of $u$ can also reach $t$: reverse the edge from that neighbor to $u$ using symmetry of adjacency (`adj_symm`), then follow the walk from $u$ to $t$. Consequently, at such a vertex the average of $F$ over neighbors equals the average of the unmodified hit-time function. The one-step bound on hit time minus its neighbor average (`hitTime_sub_avg_le`) then gives $F(u)-G.avg(F)(u)\le 1$ for $u\ne t$. If $C(u)$ fails, $F(u)=0$ and its neighbor average is nonnegative, so the same inequality follows. At $t$, the hit time is zero (`hitTime_self`), hence $F(t)=0$. Finally, any vertex where $F$ is positive must satisfy $C$, by the definition of $F$. These properties meet the hypotheses of the energy bound (`le_of_energy`), which gives $F(s)\le 2D|V|^3$. Since $s$ reaches $t$, $F(s)$ is the stated cumulative miss probability.

**Key facts.** `Randomized.RegularMultigraph.hitTime_nonneg`, `Randomized.RegularMultigraph.adj_symm`, `Randomized.RegularMultigraph.hitTime_sub_avg_le`, `Randomized.RegularMultigraph.hitTime_self`, `Randomized.RegularMultigraph.le_of_energy`.
