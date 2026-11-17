<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Basic.lean :: Kruskal.UF.init_find -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Find on the Initial State

**Claim.** In the initial union-find state, find at a node returns that node’s underlying numeric value.

**Proof.** The initial state assigns each node its underlying numeric value, and find returns the state’s value at that node. The result is therefore the node’s underlying value.
