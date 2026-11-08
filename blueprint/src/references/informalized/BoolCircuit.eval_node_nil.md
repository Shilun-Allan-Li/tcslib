<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.eval_node_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of an Empty Gate

**Claim.** A gate with no children evaluates to its gate label: an empty AND gate is true, and an empty OR gate is false.

**Proof.** If the gate is AND, its evaluation is the fold of conjunction over the empty list, whose identity value is true. If it is OR, the corresponding empty fold of disjunction has identity value false. These are exactly the two Boolean values of the gate label.
