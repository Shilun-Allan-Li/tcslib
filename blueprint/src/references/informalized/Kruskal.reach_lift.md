<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Reach.lean :: Kruskal.reach_lift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting reachability to another edge set

**Claim.** If every adjacency supplied by `edges` connects vertices that are reachable through `edges'`, then every pair reachable through `edges` is reachable through `edges'`.

**Proof.** Induct on the path through `edges`. A path of length zero is reflexive, so it is also a path through `edges'`. For a path extended by one adjacency, the induction hypothesis gives a path through `edges'` to the previous endpoint, and the assumed condition supplies a path through `edges'` for the final adjacency. Concatenating them gives the required path.
