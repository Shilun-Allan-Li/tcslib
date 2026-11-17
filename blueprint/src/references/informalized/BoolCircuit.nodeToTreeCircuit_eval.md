<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredCircuit.lean :: BoolCircuit.nodeToTreeCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by tree unrolling

**Claim.** For every layer, node, and Boolean input assignment in the stated range, the tree obtained by recursively unrolling the node evaluates to the same value as that node in the layered circuit.

**Proof.** Use induction on the layer index. At layer zero, the unrolled tree is the positive literal corresponding to the input node. Its evaluation is the assigned input value, which is also the value of the node at the input layer. Now suppose the result holds at layer $m$ and consider a node at layer $m+1$. Its unrolling is a node whose children are the recursively unrolled trees of the gate's inputs at layer $m$. By the induction hypothesis, each child evaluates to the value of its corresponding input node. The layered node's value is the gate operation applied to those same input values. By the AND/OR correctness assumption, that operation is the fold over the finite set of gate inputs using conjunction when the flag is AND and disjunction otherwise. The tree node uses precisely that fold on its children, so its evaluation agrees with the layered node's value in either case.
