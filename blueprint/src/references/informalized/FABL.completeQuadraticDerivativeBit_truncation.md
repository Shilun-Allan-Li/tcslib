<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticDerivativeBit_truncation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a truncated vector

**Claim.** For $k<n$, the derivative at coordinate $k$ of the vector formed from the first $k$ encoded bits of $w$ and zeros afterward equals the sum of those encoded bits.

**Proof.** The derivative at coordinate $k$ sums the truncated vector over all coordinates other than $k$. Since $k<n$, this is exactly the sum over coordinates filtered by being different from $k$. At each such coordinate, the truncated vector contributes the encoded bit when its index is below $k$, and zero otherwise. The excluded coordinate $k$ itself would contribute zero to the prefix sum as well, since it does not satisfy the strict inequality $k<k$. Consequently this filtered sum is precisely the sum of the encoded first $k$ bits.
