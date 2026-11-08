<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwireLeft_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound after left hardwiring

**Claim.** Hardwiring the first $m$ inputs of $C$ produces a circuit whose size is at most the size of $C$.

**Proof.** The size is in fact unchanged by hardwiring, as established by `hardwireLeft_size`; the claimed inequality follows immediately from that equality.

**Key facts.** `BoolCircuit.DAGCircuit.hardwireLeft_size`.
