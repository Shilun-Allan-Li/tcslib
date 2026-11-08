<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.transProb_succ_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Probability Sum Formula

**Claim.** For a finite regular multigraph of positive degree, the $(k+1)$-step transition probability from $u$ to $v$ equals the sum over vertices $x$ of the one-step transition probability from $u$ to $x$ times the $k$-step transition probability from $x$ to $v$.

**Proof.** By the transition probability recurrence, the left side is the average of the $k$-step transition probabilities from the indexed neighbors of $u$. The sum over those neighbors can be rewritten as a sum over vertices $x$, weighting each vertex by its multiplicity among the neighbors (`sum_nbr_eq`). Dividing by $D$ distributes across this finite sum. The one-step transition probability from $u$ to $x$ is that multiplicity divided by $D$ (`transProb_one`), so each resulting summand is exactly the product in the claim.

**Key facts.** `Randomized.RegularMultigraph.transProb_succ`, `Randomized.RegularMultigraph.sum_nbr_eq`, `Randomized.RegularMultigraph.transProb_one`.
