<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Reach.lean :: Kruskal.reach_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Endpoints of a listed edge are reachable

**Claim.** If an edge belongs to an edge list, its two endpoints are reachable through that list.

**Proof.** The edge itself witnesses symmetric adjacency between its endpoints: it belongs to the list and its endpoints match in the forward orientation. A single adjacency is a path, so the endpoints are reachable.
