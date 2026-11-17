<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.DAGCircuit.fanoutTwo_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound after fanout reduction

**Claim.** The size of the circuit obtained from $C$ by fanout reduction is at most $n+3m$, where $n$ is the number of input vertices and $m$ is the number of gates of $C$.

**Proof.** The invariant for the fanout-two construction bounds the number of constructed gates by three times the number of original gates (`foGates_inv`). The fan-in-two hypothesis supplies its required gate conditions (`gates_ok_of_isFaninTwo`), and acyclicity follows from the circuit’s topological order. The constructed circuit’s size is the number of inputs plus its number of gates. Substituting the gate-count bound therefore gives size at most $n+3m$.

**Key facts.** `BoolCircuit.gates_ok_of_isFaninTwo`, `BoolCircuit.foGates_inv`.
