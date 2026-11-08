<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.coefficientGap_mul_pow_add_higher -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-Moment Coefficient Sum Decomposition

**Claim.** If $j\leq r$ and the coefficient gaps $G_l$ vanish for every $l<j$, then the sum of $G_l t^{2l}$ over $0\leq l\leq r$ is the $j$th term plus the sum over $j<l\leq r$.

**Proof.** Let the summand at index $l$ be $G_l t^{2l}$. Partition the indices from $0$ through $r$ into those with $j<l$ and those with $j\geq l$. The latter sum has only the index $j$ contributing: every index below $j$ vanishes by the hypothesis, and $j$ itself is included because $j\leq r$. Thus the whole sum is the sum over indices above $j$ plus the $j$th term. Commuting the two real summands gives the stated order.
