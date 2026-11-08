<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.toBinary_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by binary conversion

**Claim.** For every circuit tree $c$ and input assignment $x$, the binary conversion of $c$ has the same evaluation as $c$.

**Proof.** Proceed by structural induction. For a literal, conversion leaves the literal unchanged, so the evaluations agree. For a node with children $cs$, conversion first converts each child and then combines them with the same conjunction or disjunction. The combination evaluation fact (combine_eval) identifies this combined circuit’s evaluation with that of the node on the converted children. By the induction hypotheses, each converted child has the same value as its original child. Applying the node evaluation to these pointwise equal child values gives the original node’s evaluation (eval_node_map), as required.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.combine_eval`, `BoolCircuit.eval_node_map`.
