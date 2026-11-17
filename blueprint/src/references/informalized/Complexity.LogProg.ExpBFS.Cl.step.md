<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.Cl.step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure under one transition

**Claim.** Appending one oracle-accepted transition from a reachable vertex to a vertex below $K$ preserves reachability in the specified sense.

**Proof.** Unpack the reachability of $u$ to obtain its initial vertex, the initial-query acceptance, and the path to $u$. Append the given transition from $u$ to $v$, together with its endpoint bound $v<K$, as one final edge of that path. The resulting path witnesses that $v$ is reachable from the same initial vertex.
