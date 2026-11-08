<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.GatesAcyclic.nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of the empty gate list

**Claim.** For every natural number $n$, the empty list of gates satisfies the acyclicity condition starting at $n$.

**Proof.** Acyclicity asks for the stated bound at every position in the list. The empty list has no positions, so there is no position at which the condition could fail. Hence it is acyclic for every $n$.
