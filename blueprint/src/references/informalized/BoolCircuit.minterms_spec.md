<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.minterms_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of emitted minterms

**Claim.** For any Boolean function $f$ on assignments to $n$ variables, emitting an AND tree for each satisfying assignment after the input-negation gates yields an acyclic circuit with the stated output, size, and gate-structure properties.

**Proof.** Apply the specification for emitting a list of trees (`emitTrees_spec`) to the list of minterm-leaf lists for the satisfying assignments, with the input-negation gates as the initial circuit. AND is not a NOT gate, as required by that specification, and the initial circuit is acyclic (`negInputGates_acyclic`). It remains to check that every leaf index used by these trees is available in the initial circuit's vertex range. Any listed tree comes from some satisfying assignment $u$, and any leaf in its minterm-leaf list comes from some index $i$ in `Fin n`; that leaf is the vertex selected by `litVertex n i (u i)`. Such a vertex is less than $n+n$ (`litVertex_lt`), while the initial list has $n$ gates and hence has vertices below $n+n$. Thus the emission specification applies and supplies acyclicity, the output count and bounds, the evaluation statement, the size bound, and the claimed form of newly emitted gates.

**Key facts.** `BoolCircuit.emitTrees_spec`, `BoolCircuit.negInputGates_acyclic`, `BoolCircuit.litVertex_lt`.
