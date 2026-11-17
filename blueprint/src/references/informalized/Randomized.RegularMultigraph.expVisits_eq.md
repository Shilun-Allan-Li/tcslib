<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.expVisits_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Visits and Transition Probabilities

**Claim.** For a regular multigraph of degree $D>0$, the expected number of visits to $v$ along a uniformly chosen sequence of $N$ neighbor indices starting at $u$ is the sum, for $j=0,\dots,N-1$, of the probabilities that the walk is at $v$ after $j+1$ steps.

**Proof.** Proceed by induction on $N$, with the starting vertex allowed to vary. When $N=0$, there are no visits and the sum is empty, so both sides are zero. For the successor case, the expected-visit recursion (`expVisits_succ`) decomposes the first step: average over its possible indices the indicator that this step reaches $v$, plus the expected visits over the remaining steps from the resulting neighbor. Apply the induction hypothesis to each of those remaining walks. Interchanging the finite sums and distributing the average separates the result into the sum of the averaged remaining-visit terms and the average of the first-step indicators. By the one-step transition recursion (`transProb_succ`), each remaining-visit average is the transition probability for the corresponding next step; the average of the first-step indicators is the probability of being at $v$ after one step, using the zero-step transition formula (`transProb_zero`). Combining these terms gives the stated sum through step $N$.

**Key facts.** `Randomized.RegularMultigraph.expVisits_succ`, `Randomized.RegularMultigraph.transProb_succ`, `Randomized.RegularMultigraph.transProb_zero`.
