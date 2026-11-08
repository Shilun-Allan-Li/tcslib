<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.three_quarters_le_hitProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on the Probability of Hitting a Target

**Claim.** If $D\leq 2|V|$ and there is a path from $s$ to $t$, then a uniformly chosen sequence of $100|V|^4$ neighbor indices followed from $s$ visits $t$ with probability at least $3/4$.

**Proof.** Apply the path-based estimate that the probability of missing $t$ is at most $2D|V|^3/(L+1)$ after $L$ steps (`Randomized.RegularMultigraph.one_sub_le_hitProb`). Set $L=100|V|^4$ and write $n=|V|$. From $D\leq 2n$ and $n\geq0$, we obtain $2Dn^3\leq4n^4$. Also $100n^4+1>0$, so this inequality implies $2Dn^3/(100n^4+1)\leq 1/4$. The path-based estimate therefore gives a hit probability of at least $1-1/4=3/4$, as required.

**Key facts.** `Randomized.RegularMultigraph.one_sub_le_hitProb`.
