<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Reach.lean :: Kruskal.reach_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of reachability

**Claim.** If every edge in `e1` also occurs in `e2`, then any two vertices connected through `e1` are connected through `e2`.

**Proof.** Induct on the path through `e1`. The reflexive path remains reflexive through `e2`. For an extended path, the induction hypothesis transfers the earlier part to `e2`; the final adjacency also transfers because its witnessing edge in `e1` occurs in `e2` (`symAdj_mono`). Appending that adjacency completes the path through `e2`.

**Key facts.** `Kruskal.symAdj_mono`.
