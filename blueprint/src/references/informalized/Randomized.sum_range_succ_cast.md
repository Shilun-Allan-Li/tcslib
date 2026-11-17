<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/DirectedWalk.lean :: Randomized.sum_range_succ_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of consecutive integers

**Claim.** For every natural number $N$, the rational sum of $j+1$ over $0\le j<N$ is $N(N+1)/2$.

**Proof.** Proceed by induction on $N$. For $N=0$, the sum is empty and both sides are zero. For the successor case, the sum through $j=N$ is the previous sum plus $N+1$. Substituting the induction hypothesis gives $N(N+1)/2+(N+1)=(N+1)(N+2)/2$, as required.
