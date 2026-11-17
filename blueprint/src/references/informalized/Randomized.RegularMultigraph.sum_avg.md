<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.sum_avg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Neighbor Averages

**Claim.** For a finite regular multigraph of positive degree $D$ and rational-valued function $f$ on its vertices, the sum over all vertices of the average of $f$ over the indexed neighbors equals the sum of $f$ over all vertices.

**Proof.** By the regular multigraph counting identity (`sum_swap`), summing $f$ over all indexed neighbors of all vertices gives the same total as summing, for each vertex, the values of $f$ at all vertices whose neighbor list contains it. Since each vertex occurs exactly $D$ times in the neighbor lists, the latter total is $D\sum_v f(v)$. The definition of the neighbor average divides each vertex's neighbor sum by $D$. Summing those averages therefore gives $\frac{1}{D}\,D\sum_v f(v)=\sum_v f(v)$; division is valid because the degree is positive.

**Key facts.** `Randomized.RegularMultigraph.sum_swap`.
