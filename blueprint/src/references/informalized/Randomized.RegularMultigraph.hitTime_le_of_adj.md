<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_le_of_adj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hitting Time for Adjacent Vertices

**Claim.** If $u$ and $v$ are adjacent, then for every $N$ the cumulative miss probability for hitting $v$ from $u$ through step $N-1$ is at most $D(|V|-1)$.

**Proof.** By symmetry, choose an indexed neighbor $i$ of $v$ that is $u$. The hitting time from $u$ to $v$ is therefore one term in the sum of hitting times from all indexed neighbors of $v$ to $v$. Every term is nonnegative, so this one term is at most the full sum. The return-time bound says that the average of this sum over the $D$ indexed neighbors is at most $|V|-1$ (unfolding the average and return-time definitions). Since $D>0$, multiplying by $D$ bounds the full sum by $D(|V|-1)$, and hence bounds the selected term as required.

**Key facts.** `Randomized.RegularMultigraph.adj_symm`, `Randomized.RegularMultigraph.hitTime_nonneg`, `Randomized.RegularMultigraph.returnTime_le_card`.
