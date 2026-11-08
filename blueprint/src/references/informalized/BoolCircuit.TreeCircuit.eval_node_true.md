<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.TreeCircuit.eval_node_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an AND Node

**Claim.** For every list of circuit trees and every assignment, the value of the AND node with those children equals the Boolean conjunction of their values.

**Proof.** As for the corresponding OR result, it suffices to compare when both Boolean values are true. The characterization of a true AND node (`BoolCircuit.TreeCircuit.eval_node_true_iff`) says that every child in the list evaluates to true exactly when the node does. The standard characterization of list conjunction says that `cs.all (fun c => c.eval x)` is true under precisely that same condition. Therefore the two Boolean values agree.

**Key facts.** `BoolCircuit.TreeCircuit.eval_node_true_iff`.
