<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Basic.lean :: Kruskal.processEdges_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Sweep Output

**Claim.** Every edge in the output of the edge-selection sweep was either in its initial accumulator or in the scanned edge list.

**Proof.** Induct on the scanned list, allowing the state and accumulator to vary. If the list is empty, the output is the reversed accumulator, so every output edge belongs to the accumulator. For a nonempty list, unfold the sweep and apply the induction hypothesis to the recursive output. If the first edge is kept, an edge supplied by the recursive accumulator either is that first edge, in which case it belongs to the scanned list, or was already in the old accumulator; an edge supplied by the recursive remainder belongs to the scanned list as well. If the first edge is skipped, the recursive accumulator is unchanged and the recursive remainder is a sublist of the original scanned list. These cases establish the claim.
