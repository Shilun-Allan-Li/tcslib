<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cellIdx_lt_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cell Index Bound

**Claim.** For $N,T,t\in\mathbb{N}$, a state index $\tau<k$, and $r<2T+1$, the cell index at time $t$ is less than $(t+1)$ times the configuration stride $k(2T+1)+N+3$.

**Proof.** By the cell offset bound (`Complexity.cell_off_lt`), $\tau(2T+1)+r<k(2T+1)$. The stride is $k(2T+1)+N+3$, so this offset is strictly smaller than the stride. Adding $t$ copies of the stride to both sides yields $t\,s+\tau(2T+1)+r<(t+1)s$, which is the desired bound.

**Key facts.** `Complexity.cell_off_lt`.
