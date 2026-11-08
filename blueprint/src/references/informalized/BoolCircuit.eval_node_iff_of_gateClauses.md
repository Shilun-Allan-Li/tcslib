<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.eval_node_iff_of_gateClauses -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Evaluation from Gate Clauses

**Claim.** If the clauses associated with a gate and its children are satisfied, and each child evaluates to true exactly when its gate variable is true, then the gate evaluates to true exactly when its own gate variable is true.

**Proof.** Consider first an OR gate. Its main clause says either the gate variable is false or at least one child gate variable is true; each side clause says that if the gate variable is true, then the corresponding child gate variable is true. By the assumed child equivalences, these conditions transfer to child circuit evaluations. An OR gate evaluates to true exactly when some child evaluates to true (BoolCircuit.TreeCircuit.eval_node_false_iff). Thus the main clause supplies the forward implication from the gate variable being true to an evaluated child, and the side clauses give the reverse implication from an evaluated child to the gate variable being true. For an AND gate, the main clause says either the gate variable is true or some child gate variable is false; each side clause says that if a child gate variable is false, then the gate variable is false. The gate evaluates to true exactly when every child does (BoolCircuit.TreeCircuit.eval_node_true_iff). If all children evaluate to true, the side clauses rule out the gate variable being false, so it is true. If the gate variable is true, the main clause rules out any false child, so every child evaluates to true.

**Key facts.** `BoolCircuit.TreeCircuit.eval_node_false_iff`, `BoolCircuit.TreeCircuit.eval_node_true_iff`.
