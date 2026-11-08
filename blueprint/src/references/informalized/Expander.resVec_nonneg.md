<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.resVec_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the restricted iterates

**Claim.** For every finite subset $B$, every iterate index $k$, and every coordinate $j$, the $j$th coordinate of the restricted iterate is nonnegative.

**Proof.** Proceed by induction on the iterate index. At index zero, each coordinate is either $1/n$ or zero, and both are nonnegative. For the successor step, the coordinate is a sum over $l$ of terms $(\mathbf{1}_{j\in B}A_{jl})\,r_k(l)$. The indicator-weighted matrix entry is nonnegative: it is either $A_{jl}\ge0$ or zero. By induction $r_k(l)\ge0$, so each product, and hence their finite sum, is nonnegative.
