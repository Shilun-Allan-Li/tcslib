<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.inpIdx_lt_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Index Before Next Block

**Claim.** For every $p<N+2$, the input index $t\bigl(k(2T+1)+N+3\bigr)+k(2T+1)+p$ is strictly less than $(t+1)\bigl(k(2T+1)+N+3\bigr)$.

**Proof.** Write $S=k(2T+1)+N+3$ for the block stride. The input index is $tS+k(2T+1)+p$, while the next block begins at $(t+1)S=tS+k(2T+1)+N+3$. The hypothesis $p<N+2$ gives $p<N+3$, so the input index is strictly below the next block's start.
