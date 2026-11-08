<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.isStationary_real_iff_eq_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Stationary Distributions Are Uniform

**Claim.** For a normalized real-valued distribution on a finite connected, nonbipartite regular multigraph, stationarity is equivalent to being uniform.

**Proof.** Assume first that $p$ is stationary for one step. Induction using the one-step stationarity equations and the convolution formula for transition probabilities shows that $p$ is unchanged after every number of steps; the base case uses the time-zero transition probabilities, and the induction step interchanges finite sums (`transProb_zero`, `transProb_succ_eq_sum`). Set $K=2|V|$. Connectedness and nonbipartiteness give a strictly positive lower bound for every $K$-step transition probability (`one_div_pow_le_transProb_two_mul`). Choose a vertex $v$ where $p$ is maximal. The probabilities of reaching $v$ in $K$ steps, summed over all starting vertices, equal $1$ (`sum_transProb_left`); also, stationarity at time $K$ gives $p(v)=\sum_u p(u)P^K(u,v)$. Subtracting these equalities after weighting shows
\[\sum_u (p(v)-p(u))P^K(u,v)=0.\]
Every summand is nonnegative by maximality, and each transition factor is strictly positive. Since a finite sum of nonnegative terms vanishes only when each term does, every $p(u)$ equals $p(v)$. Normalization then forces this common value to be $1/|V|$.

Conversely, for the uniform distribution, the sum of the one-step transition probabilities into any fixed vertex is $1$ (`sum_transProb_left`). Multiplying this identity by $1/|V|$ verifies the stationarity equation at that vertex.

**Key facts.** `Randomized.RegularMultigraph.transProb_zero`, `Randomized.RegularMultigraph.transProb_succ_eq_sum`, `Randomized.RegularMultigraph.one_div_pow_le_transProb_two_mul`, `Randomized.RegularMultigraph.sum_transProb_left`.
