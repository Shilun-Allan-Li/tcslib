<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.sum_map_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List and finite range sums agree

**Claim.** For every function $f:\mathbb N\to\mathbb N$ and every $V\in\mathbb N$, summing the list of its values at $0,1,\ldots,V-1$ gives the finite sum over that range.

**Proof.** Induct on $V$. When $V=0$, both sums are empty and equal zero. For the successor case, the list of indices below $V+1$ is the list below $V$ with the final entry $V$ appended. Mapping $f$ over this decomposition and summing gives the previous list sum plus $f(V)$. By the induction hypothesis the previous list sum is the finite sum over indices below $V$, and the successor formula for finite range sums identifies this with the finite sum below $V+1$.
