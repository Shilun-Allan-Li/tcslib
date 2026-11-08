<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Reach.lean :: Kruskal.reach_mem_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability depends only on edge membership

**Claim.** If two edge lists contain exactly the same edges, then they induce the same reachability relation.

**Proof.** Apply monotonicity of reachability first from `l1` to `l2`: every edge in `l1` belongs to `l2` by the forward direction of the membership equivalence. This proves that reachability through `l1` implies reachability through `l2`. The reverse direction follows in the same way using the backward direction of the equivalence.

**Key facts.** `Kruskal.reach_mono`.
