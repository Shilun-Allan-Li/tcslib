<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityTreeValue_eq_prod_fin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product formula for parity tree values

**Claim.** For every depth $t$ and index $g$, the parity tree value is the product of the padded inputs at indices $g r^t+k$ for $0\le k<r^t$.

**Proof.** We argue by induction on the depth, keeping the index $g$ arbitrary. At depth zero, there is just one index in the product, and its index is $g r^0+0=g$; the product is therefore the padded input at $g$, which is the depth-zero tree value. For the successor step, the recursion expresses the value at depth $t+1$ as the product over $j<r$ of depth-$t$ values at indices $gr+j$. Apply the induction hypothesis to each of these factors. This gives a product indexed by pairs $(j,k)$, with $j<r$ and $k<r^t$, whose padded-input indices are $(gr+j)r^t+k$. Reindex the finite product by the canonical bijection between these pairs and the indices below $r^{t+1}$ (\(FABL.parityTreeIndexEquiv_val\)). The resulting index is $g r^{t+1}+j r^t+k$, which is exactly the claimed range after the reindexing. This proves the formula at depth $t+1$, using the successor recursion (\(FABL.parityTreeValue_succ\)).

**Key facts.** `FABL.parityTreeValue_succ`, `FABL.parityTreeIndexEquiv_val`.

**Caveat.** The supplied informal statement describes circuit-size bounds, but the formal statement and proof source concern the product formula for parity tree values. The account follows the formal statement and proof.
