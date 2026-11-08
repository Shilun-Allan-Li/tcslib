<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.randProb_hits_decodeIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit String Simulation of Indexed Walks

**Claim.** If length-$b$ Boolean strings are in bijection with the $D$ neighbor indices, then for every target $t$, number of steps $k$, and starting vertex $s$, the probability that a uniformly chosen Boolean string of length $kb$, split into blocks and decoded into indices, visits $t$ equals the probability for a uniformly chosen sequence of $k$ neighbor indices.

**Proof.** First, the bijection between length-$b$ Boolean strings and neighbor indices implies that there are exactly $D$ such strings, so $2^b=D$. Proceed by induction on the number $k$ of steps. At $k=0$, both processes take no steps, and their probabilities agree: they are $1$ if the starting vertex is $t$ and $0$ otherwise. For the inductive step, split a uniformly chosen length-$(k+1)b$ string into its first block $u$ of length $b$ and the remaining string. The probability of a hit is the average over all first blocks, with each block having probability $1/2^b=1/D$. If $s=t$, a hit has already occurred, so this probability is $1$, agreeing with the indexed walk. If $s\ne t$, decoding the first block gives the neighbor index $e(u)$, and the induction hypothesis identifies the conditional probability of a later hit with the indexed-walk hit probability from $G.nbr(s,e(u))$. Averaging over all blocks gives the average over all neighbor indices, because the bijection $e$ reindexes the sum. This is precisely the one-step recurrence for the indexed-walk hit probability (`hitProb_succ`), so the two probabilities are equal.

**Key facts.** `Randomized.RegularMultigraph.hitProb_zero`, `Randomized.RegularMultigraph.hitProb_succ`, `Randomized.randProb_append`, `Randomized.decodeIdx_succ_append`.
