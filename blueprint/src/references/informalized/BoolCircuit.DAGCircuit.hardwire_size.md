<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwire_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size After Hardwiring

**Claim.** The size of the circuit obtained by hardwiring the last $m$ inputs equals the size of the original circuit.

**Proof.** Hardwiring replaces the $n+m$ input positions by $n$ input positions and adds exactly $m$ constant gates before the original gates. Thus its size is $n$ plus the number of original gates plus $m$, which is the original size $(n+m)$ plus the number of original gates. The two quantities are equal by associativity and commutativity of natural-number addition.
