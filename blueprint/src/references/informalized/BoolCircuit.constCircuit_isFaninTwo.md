<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.constCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in bound for constant circuits

**Claim.** For every natural number $n$ and Boolean value $b$, the constant circuit is well formed and every gate has at most two inputs.

**Proof.** The circuit has exactly one gate, namely the gate representing $b$. Thus, in either part of the fan-in-two condition, any gate in the circuit must be this gate. Its argument list is empty, so it has no repeated arguments and its length is at most two. Its kind is either AND or OR, never NOT, so the condition requiring a NOT gate to have exactly one argument holds vacuously. These facts give well-formedness and the fan-in bound.
