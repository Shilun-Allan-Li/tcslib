<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.eval_node_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under Child Replacement

**Claim.** Replacing each child in a finite list by a circuit with the same evaluation preserves the evaluation of the gate applied to that list.

**Proof.** Induct on the list of children. The empty list is unchanged by replacement. For a nonempty list, the induction hypothesis says that replacing the tail preserves its gate evaluation, and the hypothesis gives equal evaluations for the head and its replacement. The gate evaluation folds the child evaluations using conjunction when the gate is AND and disjunction when it is OR. Substituting the equal head values and equal tail evaluations therefore leaves the whole value unchanged in either case.
