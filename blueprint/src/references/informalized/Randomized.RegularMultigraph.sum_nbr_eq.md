<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.sum_nbr_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summing Over Neighbors by Multiplicity

**Claim.** For a finite regular multigraph of degree $D$, a vertex $u$, and rational-valued function $h$, the sum of $h$ over the $D$ neighbor indices of $u$ equals the sum over vertices $v$ of the number of indices leading from $u$ to $v$ multiplied by $h(v)$.

**Proof.** Group the sum over neighbor indices according to their destination vertex. For each vertex $v$, exactly $\mathrm{mult}(u,v)$ indices have neighbor $v$, and each contributes the same value $h(v)$. Thus the contribution of that fiber is $\mathrm{mult}(u,v)h(v)$; summing these contributions over all vertices gives the stated identity.
