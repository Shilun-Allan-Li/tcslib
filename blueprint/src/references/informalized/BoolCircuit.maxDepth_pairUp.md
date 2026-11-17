<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.maxDepth_pairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of Paired Circuits

**Claim.** Pairing consecutive circuits into gates increases the maximum depth by at most one.

**Proof.** Proceed by induction on the list, splitting it into the empty list, a singleton, or a list beginning with two circuits. The empty list has maximum depth zero, and a singleton is unchanged, so both bounds follow directly. In the two-circuit case, the new leading gate has depth one plus the maximum of the depths of its two children: this follows from the depth formula for a node (`BoolCircuit.TreeCircuit.depth_node`) and the list maximum formulas (`BoolCircuit.TreeCircuit.maxDepth_cons`, `BoolCircuit.TreeCircuit.maxDepth_nil`). The induction hypothesis bounds the maximum depth of the paired remainder by one plus the maximum depth of the original remainder. Combining these bounds with the leading gate’s depth gives the claimed inequality for the whole list.

**Key facts.** `BoolCircuit.TreeCircuit.depth_node`, `BoolCircuit.TreeCircuit.maxDepth_cons`, `BoolCircuit.TreeCircuit.maxDepth_nil`.
