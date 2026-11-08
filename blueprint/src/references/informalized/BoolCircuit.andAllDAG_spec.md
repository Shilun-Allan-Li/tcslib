<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.andAllDAG_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of the AND circuit

**Claim.** For each natural number $n$, the recursively emitted circuit combines inputs $0,dots,n-1$ with AND and satisfies the stated bounds and structural properties.

**Proof.** Apply the general specification of the recursive tree emitter (`BoolCircuit.emitTree_spec`) with AND as the gate kind, the input list $[0,1,\ldots,n-1]$, and the empty initial gate list. AND is not NOT, as required by that result. The empty list is acyclic (`BoolCircuit.GatesAcyclic.nil`), and every vertex in the input list is less than $n$, so it is a valid input vertex for the emitter. The general specification therefore gives the claimed extension, acyclicity, output bound, evaluation as the conjunction of the inputs, gate-count and depth bounds, and the stated properties of every newly emitted gate.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.emitTree_spec`.
