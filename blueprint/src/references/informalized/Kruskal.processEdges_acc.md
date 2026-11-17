<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Optimality.lean :: Kruskal.processEdges_acc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accumulator Splits Off as a Reversed Prefix

**Claim.** For any edge list, initial state, and accumulator, the sweep’s output is the reversed accumulator followed by the output from the same sweep with an empty accumulator.

**Proof.** Induct on the scanned edge list, allowing the state and accumulator to vary. With no edges left, the sweep returns the reversed accumulator, which is the reversed accumulator concatenated with the empty-accumulator output. For a nonempty list, consider its first edge. If its endpoints have different representatives, both runs keep the edge and continue with the state obtained by merging its endpoints. Apply the induction hypothesis to the run with accumulator formed by putting this edge first, and also to the empty-accumulator run; reversing and concatenating these prefixes gives the claimed identity. If the endpoints already have the same representative, both runs skip the edge and continue with their respective unchanged states and accumulators, so the induction hypothesis gives the result directly.
