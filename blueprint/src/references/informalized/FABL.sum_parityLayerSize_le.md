<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.sum_parityLayerSize_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Layer Size Bound

**Claim.** If $r\ge1$ and $h>0$, and the size of layer $k$ is $r^k2^r$, then the sum of these sizes over $0\le k<h$ is at most $h r^{h-1}2^r$.

**Proof.** For each $k<h$, we have $k\le h-1$. Since $r\ge1$, powers of $r$ are nondecreasing in the exponent, so $r^k2^r\le r^{h-1}2^r$. There are exactly $h$ indices in the range, and hence their sum is at most $h$ times this common upper bound.
