<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGCircuit.deconst_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by eliminating constants

**Claim.** For a circuit with positive input count satisfying the stated well-formedness and fan-in hypotheses, every input assignment gives the same output in the circuit obtained by eliminating constants as in the original circuit.

**Proof.** The value-preservation theorem for the transformation (`DAGCircuit.deconst_values`) states that every original vertex $v<n+|C|$ has the same value at its shifted index in the transformed circuit. Apply it to the original output vertex, which is within that range by the circuit's output condition. The shifted output is exactly the output chosen for the transformed circuit, so the two circuits' outputs agree.

**Key facts.** `BoolCircuit.DAGCircuit.deconst_values`.
