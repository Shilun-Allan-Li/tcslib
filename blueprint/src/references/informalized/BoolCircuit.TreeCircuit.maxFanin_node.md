<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.maxFanin_node -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum fanin of a circuit node

**Claim.** For a node with child list $cs$, its maximum fanin is the maximum of the number of children and the largest maximum fanin among those children, taking the empty-list maximum to be $0$.

**Proof.** Unfold the definition of maximum fanin for a node: it is the maximum of the child-list length and the right fold that takes the maximum of each child's fanin, starting at $0$. That fold is exactly the maximum fanin aggregated over $cs$, giving the stated equality.
