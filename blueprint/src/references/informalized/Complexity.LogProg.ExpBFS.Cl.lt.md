<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.Cl.lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on reachable vertices

**Claim.** Any vertex reachable through the specified initial and step oracle queries is less than $K$.

**Proof.** Unpack reachability to obtain an initial vertex $u<K$ and a reflexive-transitive path from $u$ to $v$ whose transitions each end below $K$. Split the path into its final-tail cases. If the path is empty, then $v=u$, so the initial bound gives $v<K$. Otherwise, its last transition explicitly includes the fact that its endpoint is below $K$, which is the desired bound.
