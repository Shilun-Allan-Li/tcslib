<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Optimality.lean :: Kruskal.ufAfterProcessEdges_partition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Greedy and unconditional merging

**Claim.** Processing the edges greedily, merging endpoints only when their representatives differ, yields a state with the same partition as merging every edge unconditionally in order.

**Proof.** Induct on the edge list, with an arbitrary initial state. For the empty list, both procedures leave the state unchanged, so their induced partitions agree. For a nonempty list with head edge $e$, if its endpoints have different representatives, both procedures merge them and then process the remaining edges; the induction hypothesis identifies the resulting partitions. If their representatives agree, the greedy procedure skips the merge. The merge is then a no-op (\texttt{Kruskal.merge_noop}), so the unconditional procedure's state before processing the remaining edges is the same state. Applying the induction hypothesis again proves equality of the final partitions.

**Key facts.** `Kruskal.UF.SamePartition.rfl`, `Kruskal.merge_noop`.
