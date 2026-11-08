<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Basic.lean :: Kruskal.UF.find_def -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Find Equals Direct Lookup

**Claim.** For any union-find state and node, the representative returned by find is the state’s value at that node.

**Proof.** By definition, find evaluates the union-find state at the given node. Thus its result is exactly the direct lookup of that state.
