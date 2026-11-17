<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.not_mem_succ_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonmembership after one additional step

**Claim.** The vertex $v$ is not reachable in at most $L+1$ steps from any initial vertex below $K$ exactly when every vertex reachable in at most $L$ steps from such a start differs from $v$ and has no edge to $v$.

**Proof.** By the one-step decomposition of reachability (`Complexity.LogProg.ISCount.mem_succ_iff`), reaching $v$ within $L+1$ steps means either that $v$ was already reachable within $L$ steps, or that some vertex $u$ reachable within $L$ steps has an edge to $v$ and $v<K$. The finset `ball` consists exactly of the vertices reachable within $L$ steps (`Complexity.LogProg.ISCount.mem_ball`). Thus, if $v$ is not reachable within $L+1$ steps, each $u$ in the ball must differ from $v$—otherwise $v$ itself was already reachable—and must not satisfy $R(u,v)$, since $v<K$. Conversely, if every $u$ in the ball has both properties, neither alternative in the one-step decomposition can hold: the first would put $v$ in the ball, and the second would give a ball element with an edge to $v$.

**Key facts.** `Complexity.LogProg.ISCount.mem_succ_iff`, `Complexity.LogProg.ISCount.mem_ball`.
