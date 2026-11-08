<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Optimality.lean :: Kruskal.processEdges_skip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping an intra-component edge

**Claim.** If the endpoints of the first edge already have the same representative, processing that edge followed by the remaining list produces the same selected edge list as processing the remaining list alone.

**Proof.** The sweep tests whether the endpoints have different representatives. The hypothesis says they do not, so the sweep takes its skip branch: it leaves the union-find state and empty accumulator unchanged and processes `rest`. This is exactly the sweep on `rest` from the original state and empty accumulator.
