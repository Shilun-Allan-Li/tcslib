<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.toBinary_size_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict size bound for binary conversion

**Claim.** For every circuit tree $c$, the size of its binary conversion plus one is at most three times the size of $c$.

**Proof.** Proceed by structural induction. For a literal, conversion leaves it unchanged, and the claimed inequality follows directly from the size of a literal. At a node with children $cs$, the size bound for combining a list (combine_size) bounds the converted node by the sum of the converted-child sizes, the number of children, and one. The induction hypotheses, summed over the children using sumSize_map_toBinary, bound the converted-child size sum together with the child count by three times the original children’s size sum. The node size formula (TreeCircuit.size_node) adds one to the original children’s sum; combining these inequalities yields that the converted node’s size plus one is at most three times its original size.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.combine_size`, `BoolCircuit.sumSize_map_toBinary`, `BoolCircuit.TreeCircuit.size_node`.
