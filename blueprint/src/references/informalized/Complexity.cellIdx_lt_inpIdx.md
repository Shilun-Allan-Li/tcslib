<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cellIdx_lt_inpIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cell Indices Precede Input Indices

**Claim.** For each time $t$, state index $\tau<k$, row index $r<2T+1$, and natural number $p$, the cell index $ts+\tau(2T+1)+r$ is strictly smaller than the input index $ts+k(2T+1)+p$, where $s=k(2T+1)+N+3$.

**Proof.** The cell offset bound (`Complexity.cell_off_lt`) gives $\tau(2T+1)+r<k(2T+1)$ from the bounds on $\tau$ and $r$. Adding the common nonnegative term $ts$ preserves strict inequality. Since $p\geq 0$, the input offset $k(2T+1)+p$ is at least $k(2T+1)$. Thus the cell index is strictly below the input index.

**Key facts.** `Complexity.cell_off_lt`.
