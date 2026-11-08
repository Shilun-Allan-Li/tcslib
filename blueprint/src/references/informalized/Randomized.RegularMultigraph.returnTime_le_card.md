<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.returnTime_le_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Truncated Return Time

**Claim.** For a finite regular multigraph of positive degree and a vertex $t$, one plus the average over the neighbors of $t$ of the sum of miss probabilities at times $0$ through $N-1$ is at most $|V|$.

**Proof.** Let $F(s)$ be the cumulative miss probability through time $N-1$ from vertex $s$. The sum over all vertices of $F(s)-\mathrm{avg}(F)(s)$ is zero, because the total of neighbor averages equals the total of the function itself (`sum_avg`). Separate the term at $t$ from the remaining vertices. For every $s\ne t$, the difference $F(s)-\mathrm{avg}(F)(s)$ is at most $1$ (`hitTime_sub_avg_le`), so the sum of these differences is at most the number of vertices other than $t$. Also, $F(t)=0$ (`hitTime_self`). Using the zero total, these bounds, and $|V\setminus\{t\}|+1=|V|$, rearrangement gives $1+\mathrm{avg}(F)(t)\le |V|$, as claimed.

**Key facts.** `Randomized.RegularMultigraph.sum_avg`, `Randomized.RegularMultigraph.hitTime_sub_avg_le`, `Randomized.RegularMultigraph.hitTime_self`.
