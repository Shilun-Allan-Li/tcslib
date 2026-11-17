<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.TreeCircuit.eval_node_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an OR Node

**Claim.** For every list of circuit trees and every assignment, the value of the OR node with those children equals the Boolean disjunction of their values.

**Proof.** The result is an equality of Booleans, so it suffices to show that the two sides are true under exactly the same condition. The characterization of a true OR node (`BoolCircuit.TreeCircuit.eval_node_false_iff`) says that its value is true exactly when some child in the list evaluates to true. The standard characterization of list disjunction says that `cs.any (fun c => c.eval x)` is true under precisely the same condition. Thus both sides have the same truth value, and hence are equal.

**Key facts.** `BoolCircuit.TreeCircuit.eval_node_false_iff`.
