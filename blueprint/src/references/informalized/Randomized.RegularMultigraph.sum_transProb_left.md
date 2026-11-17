<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.sum_transProb_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Transition Probability into a Vertex

**Claim.** For every vertex and every nonnegative number of steps, the sum over starting vertices of the probability of ending at that vertex is $1$.

**Proof.** Proceed by induction on the number of steps. At zero steps, the transition probability is $1$ when the starting vertex is the specified destination and $0$ otherwise, so summing over starting vertices gives $1$. For the successor step, express the transition probability as the neighbor average of the preceding-step probabilities (`Randomized.RegularMultigraph.transProb_succ`). Summing these averages over starting vertices preserves the sum of the averaged function (`Randomized.RegularMultigraph.sum_avg`). The induction hypothesis says that this sum of preceding-step probabilities is $1$, proving the successor case.

**Key facts.** `Randomized.RegularMultigraph.transProb_zero`, `Randomized.RegularMultigraph.transProb_succ`, `Randomized.RegularMultigraph.sum_avg`.
