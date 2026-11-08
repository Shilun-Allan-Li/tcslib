<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwire_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound After Hardwiring

**Claim.** The size of the circuit obtained by hardwiring the last $m$ inputs is at most the size of the original circuit.

**Proof.** The size after hardwiring is in fact equal to the original size, by the size-preservation result (`BoolCircuit.DAGCircuit.hardwire_size`). Equality implies the stated inequality.

**Key facts.** `BoolCircuit.DAGCircuit.hardwire_size`.
