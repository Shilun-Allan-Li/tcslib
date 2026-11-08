<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Optimality.lean :: Kruskal.processEdges_same_partition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Edge Selection Preserves the Partition

**Claim.** Merging the edges retained by the sweep into the initial state induces the same partition as merging every input edge into that state.

**Proof.** The proof first reduces the goal to the corresponding partition statement for the state produced by the sweep, using the fact that this state has the same partition as merging all the input edges (`Kruskal.ufAfterProcessEdges_partition`). It then inducts on the input list. For an empty list, the sweep and the merge process leave the state unchanged. For a nonempty list, if the first edge joins different components, the sweep keeps it; the accumulator identity (`Kruskal.processEdges_acc`) identifies the retained list as that edge followed by the tail’s retained edges, and the induction hypothesis handles the tail from the merged state. If the edge joins nodes already in the same component, the sweep skips it, and the induction hypothesis on the tail applies to the unchanged state.

**Key facts.** `Kruskal.ufAfterProcessEdges_partition`, `Kruskal.processEdges_acc`.

**Caveat.** The supplied material gives only the statement, not the definition, of `ufAfterProcessEdges`; accordingly, the initial reduction to that state’s partition and its relationship to the sweep cannot be explained more explicitly from the provided proof context.
