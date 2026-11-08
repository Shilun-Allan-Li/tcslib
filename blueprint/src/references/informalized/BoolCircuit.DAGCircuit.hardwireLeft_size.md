<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwireLeft_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size after left hardwiring

**Claim.** Hardwiring the first $m$ inputs of $C$ leaves its size unchanged, where size is the number of inputs plus the number of gates.

**Proof.** The new circuit has $n$ inputs and has $m$ inserted constant gates followed by one remapped copy of each gate of $C$. Thus its size is $n+m+|C.gates|$, which equals $(m+n)+|C.gates|$, the size of $C$.
