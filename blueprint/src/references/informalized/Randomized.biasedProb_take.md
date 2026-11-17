<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedProb_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Probability of an Initial Segment Event

**Claim.** For any real $\rho$, nonnegative integers $n,t$, and predicate $P$, the biased probability that the first $n$ entries of a string of length $n+t$ satisfy $P$ equals the biased probability of $P$ on strings of length $n$.

**Proof.** Induct on $n$, allowing $P$ to vary. When $n=0$, taking the first zero entries always gives the empty string, so the event is constant; its probability at length $t$ is the same as its probability at length zero. For the step, write $n+1+t=(n+t)+1$ and expand each side by the recursion for biased probability (`Randomized.biasedProb_succ`). In the true first-bit branch, taking the first $n+1$ entries amounts to prefixing true to the first $n$ entries of the tail; in the false branch it amounts to prefixing false. Apply the induction hypothesis to each branch, with the corresponding prefixed predicate. The two weighted branch expressions then coincide.

**Key facts.** `Randomized.biasedProb_succ`.
