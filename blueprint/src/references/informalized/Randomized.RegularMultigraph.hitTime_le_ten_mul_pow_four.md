<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_le_ten_mul_pow_four -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Hitting-Time Bound

**Claim.** If $D\le2|V|$ and $t$ is reachable from $s$ by adjacency steps, then for every $N$ the cumulative miss probability for hitting $t$ from $s$ through step $N-1$ is at most $10|V|^4$.

**Proof.** Reachability gives the bound $\operatorname{hitTime}(t,N,s)\le2D|V|^3$. Substituting $D\le2|V|$ yields $\operatorname{hitTime}(t,N,s)\le4|V|^4$. Since $|V|^4\ge0$, this is at most $10|V|^4$, proving the stated estimate.

**Key facts.** `Randomized.RegularMultigraph.hitTime_le`.
