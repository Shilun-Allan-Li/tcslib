<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.mem_ball -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Reachable Set

**Claim.** A vertex belongs to the reachable set exactly when there is an initial vertex below $K$ from which it can be reached by a walk of length at most $L$.

**Proof.** The reachable set is defined as the numbers below $K$ that satisfy the reachability predicate. Membership in the filtered finite set therefore means both that $t<K$ and that such an initial vertex and walk exist. The reachability predicate itself already implies $t<K$ (the bound on reachable vertices, `Mem.lt`), so the latter condition alone implies membership as well. This proves both directions.

**Key facts.** `Complexity.LogProg.ISCount.Mem.lt`.
