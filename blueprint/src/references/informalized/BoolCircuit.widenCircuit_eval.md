<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.widenCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under a Wider Input Space

**Claim.** Widening a circuit from $m$ variables to $n$ variables preserves its evaluation when each original input $i$ is assigned the value of the wider input at the corresponding index.

**Proof.** Proceed by induction on the circuit (`BoolCircuit.TreeCircuit.ind`). For a literal, widening only casts its index into the larger input type and retains its sign, so its evaluation is exactly the original literal's evaluation under the restricted assignment. For a node, widening maps the construction over its list of child circuits. The node evaluates by folding conjunctions or disjunctions over that list; mapping and then folding gives the same result as folding the original list, because by the induction hypothesis each child has the same evaluation under the two assignments. This applies to either kind of node.

**Key facts.** `BoolCircuit.TreeCircuit.ind`.
