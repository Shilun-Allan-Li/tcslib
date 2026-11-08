<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.DAGCircuit.IsFaninTwo.dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual Preserves Fan-In Bounds

**Claim.** Let $C$ be a finite Boolean circuit whose gates have pairwise distinct arguments, whose NOT gates have exactly one argument, and whose gates have at most two arguments. If the dual circuit is formed by swapping AND and OR gates while leaving NOT gates and all arguments unchanged, then it also has pairwise distinct gate arguments, exactly one argument at each NOT gate, and at most two arguments at every gate.

**Proof.** Write the fan-in-two hypothesis as the conjunction of well-formedness and the bound of two on every gate's argument count. Each gate in the dual list is the dual of a gate of $C$. Its argument list is unchanged, so distinctness is preserved. If that dual gate is NOT, its original gate was also NOT, since duality fixes NOT; hence it has exactly one argument by well-formedness of $C$. Finally, the same unchanged argument list has length at most two by the original fan-in bound. These facts establish both parts of the fan-in-two condition for the dual circuit.
