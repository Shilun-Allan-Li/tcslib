<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkPad.lean :: Randomized.padGraph_reflTransGen_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability in the padded graph

**Claim.** There is a finite padded-graph path from $s$ to $t$, allowing length zero, exactly when there is a finite sequence of $r$-related steps from $s$ to $t$, also allowing length zero.

**Proof.** For a padded-graph path, induct on its sequence of steps. A length-zero path is already an $r$-reflexive-transitive path. At each additional adjacency step, the adjacency characterization (`Randomized.padGraph_adj_iff`) says its endpoints are equal or $r$-related. In the equality case the path's endpoint does not change, so the induction hypothesis suffices; in the related case append that $r$-step. Conversely, each $r$-step is a padded-graph adjacency by the same characterization, so every finite sequence of such steps transfers to the padded graph, preserving the reflexive-transitive closure.

**Key facts.** `Randomized.padGraph_adj_iff`.
