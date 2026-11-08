<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.idxProb_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recurrence for Index Probability

**Claim.** For a positive alphabet size $D$, the probability that a uniformly chosen length-$(k+1)$ sequence satisfies $A$ is $1/D$ times the sum over initial symbols $i$ of the probability that a uniformly chosen length-$k$ sequence satisfies $A$ after prepending $i$.

**Proof.** Unfold the probability as the number of satisfying words divided by $D^{k+1}$. Reindex each word of length $k+1$ by its first symbol $i$ and its remaining length-$k$ word. This is a bijective decomposition, so the count of satisfying words is the sum, over $i$, of the counts of tails for which the prepended word satisfies $A$. Dividing each such count by $D^k$ gives the corresponding length-$k$ probability; since $D^{k+1}=D^kD$ and $D
e0$, the stated recurrence follows.
