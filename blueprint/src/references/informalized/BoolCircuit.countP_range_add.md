<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.countP_range_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting a shifted range

**Claim.** For natural numbers $c,u,k$, the number of indices $j$ with $0\le j<k$ and $u=c+j$ is $1$ if $c\le u<c+k$, and $0$ otherwise.

**Proof.** Proceed by induction on $k$. For $k=0$, the range contains no indices, and the interval condition $c\le u<c$ is impossible, so both sides are zero. For the step from $k$ to $k+1$, the range consists of the previous range together with the new endpoint $k$. By the induction hypothesis, the previous terms contribute one exactly when $c\le u<c+k$. The endpoint contributes one precisely when $u=c+k$. These disjoint possibilities together are exactly $c\le u<c+(k+1)$, and otherwise there is no contributing index.
