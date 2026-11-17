<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwire_isWellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formedness Under Hardwiring

**Claim.** If every gate of a circuit has distinct input vertices and every NOT gate has exactly one input, the circuit obtained by hardwiring the last inputs has the same properties.

**Proof.** Take any gate in the hardwired circuit. Its list of gates is the concatenation of the newly added constant gates and the original gates, so the gate lies in one of these two parts. If it is an added constant gate, it has no inputs, hence its input list has no repetitions; moreover, its kind is AND or OR, never NOT, so the condition on NOT gates holds vacuously. This uses the fact that a constant gate is not a NOT gate (`BoolCircuit.constGate_kind_ne_not`). If instead the gate is an original gate, both required properties follow directly from the assumed well-formedness of the original circuit.

**Key facts.** `BoolCircuit.constGate_kind_ne_not`.
