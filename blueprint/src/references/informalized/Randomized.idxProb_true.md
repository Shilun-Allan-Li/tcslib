<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.idxProb_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Certain Event

**Claim.** For $D>0$, the probability assigned to the predicate that holds for every length-$k$ sequence is $1$.

**Proof.** Every function from the $k$ positions to the $D$-symbol alphabet satisfies the predicate, so the filtered set of sequences is the entire set. There are $D^k$ such functions, and the defining denominator is also $D^k$. Since $D>0$, this denominator is nonzero, and their ratio is $1$.
