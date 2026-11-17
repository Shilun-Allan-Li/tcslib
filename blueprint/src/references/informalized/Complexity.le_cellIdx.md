<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.le_cellIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound for a cell index

**Claim.** For every time $t$, tape index $\tau$, and position $r$, the cell index $I$ is at least $t$ times the configuration stride $S$.

**Proof.** By definition, $I=tS+\tau(2T+1)+r$. The latter two summands are natural numbers and hence nonnegative, so adding them to $tS$ cannot decrease it. Therefore $tS\le I$.
