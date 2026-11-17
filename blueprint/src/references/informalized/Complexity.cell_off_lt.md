<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cell_off_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cell Offset Bound

**Claim.** If $\tau<k$ and $r<2T+1$, then $\tau(2T+1)+r<k(2T+1)$.

**Proof.** Since $\tau<k$, we have $\tau+1\leq k$. Multiplying by the positive quantity $2T+1$ gives $(\tau+1)(2T+1)\leq k(2T+1)$. The row bound gives $r<2T+1$, so $\tau(2T+1)+r<\tau(2T+1)+(2T+1)=(\tau+1)(2T+1)$. Combining these inequalities proves the claim.
