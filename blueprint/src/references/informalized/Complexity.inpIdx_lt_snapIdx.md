<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.inpIdx_lt_snapIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Index Before Snapshot

**Claim.** For every $p<N+2$, the input index $t\bigl(k(2T+1)+N+3\bigr)+k(2T+1)+p$ is strictly less than the snapshot index $t\bigl(k(2T+1)+N+3\bigr)+k(2T+1)+N+2$.

**Proof.** The two indices share the same time-block offset and the same work-tape offset. After canceling those common terms, the desired inequality is exactly $p<N+2$, which is the hypothesis.
