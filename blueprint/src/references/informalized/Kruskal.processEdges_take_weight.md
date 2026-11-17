<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Optimality.lean :: Kruskal.processEdges_take_weight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight of an accepted edge

**Claim.** When the endpoints of the first edge lie in different components, the total weight selected from the list is the edge's weight plus the total weight selected from the remaining list after merging those components.

**Proof.** Since the endpoints have different representatives, the sweep accepts the first edge, merges its endpoint components, and continues on `rest` with that edge in the accumulator. The accumulator identity (`processEdges_acc`) expresses this result as the reverse of the singleton accumulator followed by the sweep on `rest` with an empty accumulator. The reverse of a singleton list is the same singleton list. Taking total weights therefore gives the first edge's weight plus the total weight of the sweep on `rest` from the merged state.

**Key facts.** `Kruskal.processEdges_acc`.
