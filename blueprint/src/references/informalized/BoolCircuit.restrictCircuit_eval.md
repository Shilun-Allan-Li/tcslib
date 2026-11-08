<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.restrictCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation After Circuit Restriction

**Claim.** For every assignment $y$ to the first $m$ variables, the restricted circuit evaluates at $y$ to the same value as the original circuit on the assignment that uses $y$ below index $m$ and the padding assignment at indices at least $m$.

**Proof.** Induct on the circuit. For a literal, split according to whether its variable index is below $m$. In the first case restriction keeps the literal, and the extended assignment agrees with $y$ at that index. In the second case restriction replaces the literal by a constant node whose value is the literal's value under the padding assignment; the extended assignment uses that same padding value at the index. The empty-node evaluation is exactly its connective bit (`eval_node_nil`), so this replacement has the required value.

For a node, restriction preserves its connective and applies recursively to every child. The induction hypothesis gives equality of the restricted and extended evaluations for each child. Applying that equality term by term in the conjunction or disjunction fold proves equality for the whole node.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.eval_node_nil`.
