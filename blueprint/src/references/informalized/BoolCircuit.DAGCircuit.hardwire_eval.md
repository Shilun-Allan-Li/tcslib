<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwire_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation after hardwiring inputs

**Claim.** Evaluating the circuit obtained by hardwiring the last $m$ inputs to $y$ at $x$ gives the same output as evaluating $C$ at $(x,y)$.

**Proof.** The value lists of the two circuits agree: `hardwire_values` identifies the values of the hardwired circuit at $x$ with the values of $C$ at the concatenated assignment $(x,y)$. Evaluation reads the value at the circuit's output vertex, using the same default if that index is out of range. Applying this lookup to the equal value lists proves the claim.

**Key facts.** `BoolCircuit.DAGCircuit.hardwire_values`.
