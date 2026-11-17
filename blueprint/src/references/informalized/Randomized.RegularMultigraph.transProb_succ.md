<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.transProb_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Probability Recurrence

**Claim.** The probability that a walk of $k+1$ steps from $u$ ends at $v$ is the average over the $D$ neighbor indices at $u$ of the probability that a $k$-step walk from the selected neighbor ends at $v$.

**Proof.** Apply the recurrence for index probabilities (`Randomized.idxProb_succ`) to the event that the walk endpoint is $v$. This expresses the probability as a sum over first-step indices, divided by $D$. For each index $i$, a walk whose first index is $i$ has endpoint equal to the endpoint of the remaining $k$ indices starting from $G.nbr(u,i)$. Thus each summand is the corresponding $k$-step transition probability, and the sum divided by $D$ is precisely the stated average.

**Key facts.** `Randomized.idxProb_succ`.
