<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/DirectedWalk.lean :: Randomized.hitProb_chainDigraph_le_aux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chain Hitting-Probability Bound

**Claim.** For all natural numbers $n,k$ and every vertex $i\in\mathrm{Fin}(n+1)$, the $k$-step probability of hitting the last vertex from $i$, multiplied by $2^n$, is at most $2^i+k$.

**Proof.** Induct on $k$, proving the bound for every starting vertex at each stage. At time zero, the probability is $1$ at the target and $0$ elsewhere, so the claimed inequality follows in either case. For the induction step, if the starting vertex is the target, its hitting probability remains $1$, and the bound follows from $k+1\ge 0$. Otherwise its index $i$ is strictly less than $n$. In the chain digraph its outgoing neighbors are exactly $0$ and $i+1$, so its next-step hitting probability is the average of the probabilities from those two vertices (the chain average formula, `Randomized.avgOut_chainDigraph`). Apply the induction hypothesis at $0$ and at $i+1$: after multiplying the average by $2^n$, the resulting upper bound is $\bigl((1+k)+(2^{i+1}+k)\bigr)/2=2^i+k+\tfrac12$, which is at most $2^i+k+1$.

**Key facts.** `Randomized.avgOut_chainDigraph`.
