<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.sum_sq_eq_energy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Differences and Energy

**Claim.** For a finite regular multigraph of positive degree and a rational-valued function on its vertices, the sum of squared differences across all indexed neighbor pairs equals $2D$ times the sum of each vertex value multiplied by its difference from its neighbor average.

**Proof.** For each vertex and neighbor index, expand the square as $(F(u)-F(v))^2=F(u)(F(u)-F(v))+F(v)(F(v)-F(u))$, where $v$ is the indexed neighbor of $u$. Summing gives two double sums. The symmetry of the neighbor sum ( `Randomized.RegularMultigraph.sum_swap` ) identifies the second double sum with the first, so their total is twice the sum of $F(u)(F(u)-F(G.nbr(u,i)))$. For each fixed $u$, summing the inner difference over the $D$ indices gives $D F(u)-[0m\sum_i F(G.nbr(u,i))$. Since the neighbor average is that latter sum divided by $D$, this is $D(F(u)-\mathrm{avg}(F,u))$. Summing over vertices and factoring out the constants yields the claimed identity. Positivity of $D$ ensures division by $D$ is valid.

**Key facts.** `Randomized.RegularMultigraph.sum_swap`.
