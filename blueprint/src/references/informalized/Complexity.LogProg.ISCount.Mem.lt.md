<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.Mem.lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vertex Bound for Reachable States

**Claim.** Every vertex in the specified membership set is less than $K$.

**Proof.** Membership supplies an initial vertex $u<K$ satisfying the initial predicate, together with a walk of length at most $L$ from $u$ to $t$. The walk bound lemma states that if its starting vertex is below $K$, then its endpoint is also below $K$ (Complexity.LogProg.ISCount.walkLe_lt). Applying it to this walk gives $t<K$.

**Key facts.** `Complexity.LogProg.ISCount.walkLe_lt`.
