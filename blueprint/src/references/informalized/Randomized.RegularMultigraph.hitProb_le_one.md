<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.hitProb_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hit Probability Is at Most One

**Claim.** For a regular multigraph of degree $D>0$ and vertices $s,t$, the probability that a uniformly chosen sequence of $k$ neighbor indices starting at $s$ visits $t$ is at most $1$.

**Proof.** The number of sequences that hit $t$ is at most the total number of length-$k$ sequences. There are $D^k$ such sequences, and the probability is the number that hit $t$ divided by this positive total. The resulting ratio is at most $1$.
