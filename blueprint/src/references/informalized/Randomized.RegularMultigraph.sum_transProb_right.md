<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.sum_transProb_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Transition Probability from a Vertex

**Claim.** For every starting vertex and every nonnegative number of steps, the sum over destination vertices of the transition probabilities is $1$.

**Proof.** Proceed by induction on the number of steps, allowing the starting vertex to vary in the induction hypothesis. At zero steps, the transition probability is $1$ for the starting vertex itself and $0$ for every other destination (`Randomized.RegularMultigraph.transProb_zero`), so the sum is $1$. For the successor step, write each transition probability as the average, over the first-step neighbors, of the remaining transition probabilities (`Randomized.RegularMultigraph.transProb_succ`). Interchange the finite sums over destinations and neighbor indices. For each fixed neighbor, the induction hypothesis says that the sum over destinations of the remaining transition probabilities is $1$. Averaging these values gives $1$, since the average of the constant function $1$ is $1.

**Key facts.** `Randomized.RegularMultigraph.transProb_zero`, `Randomized.RegularMultigraph.transProb_succ`.
