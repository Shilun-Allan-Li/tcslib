<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.TreeCircuitFamily.language_toDAG -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Language preservation under tree-to-DAG conversion

**Claim.** For every family of Boolean tree circuits, the language recognized by its associated DAG circuit family equals the language recognized by the tree-circuit family.

**Proof.** To prove equality of the two languages, take an arbitrary word $w$ and compare membership on both sides. Membership in the DAG-family language is equivalent to the converted circuit at input length $|w|$ evaluating to true on the assignment read from $w$; this is the membership characterization for DAG-family languages. The tree-to-DAG evaluation theorem identifies that value with the original tree circuit's evaluation. By the membership characterization for tree-family languages, this is equivalent to $w$ belonging to the tree-family language. Thus the two languages have the same members.

**Key facts.** `BoolCircuit.DAGCircuitFamily.mem_language_iff`, `BoolCircuit.TreeCircuit.toDAG_eval`, `BoolCircuit.TreeCircuitFamily.mem_language_iff`.
