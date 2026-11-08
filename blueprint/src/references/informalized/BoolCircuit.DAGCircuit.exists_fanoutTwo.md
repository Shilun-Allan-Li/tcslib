<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.DAGCircuit.exists_fanoutTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-Fanout Equivalent Circuit

**Claim.** A well-formed circuit with at most two arguments per gate has an equivalent circuit satisfying those same conditions, with fanout at most two and size at most three times the original size.

**Proof.** Take the circuit produced by the fanout-two construction. It remains well-formed and has at most two arguments per gate (`BoolCircuit.DAGCircuit.fanoutTwo_isFaninTwo`), and every vertex has fanout at most two (`BoolCircuit.DAGCircuit.fanoutTwo_hasFanoutTwo`). The construction preserves the computed function on every input (`BoolCircuit.DAGCircuit.fanoutTwo_eval`). Its gate-count bound gives size at most $n+3|C.gates|$, which is at most $3(n+|C.gates|)$; since size is $n+|C.gates|$, this is the claimed bound (`BoolCircuit.DAGCircuit.fanoutTwo_size_le`).

**Key facts.** `BoolCircuit.DAGCircuit.fanoutTwo_isFaninTwo`, `BoolCircuit.DAGCircuit.fanoutTwo_hasFanoutTwo`, `BoolCircuit.DAGCircuit.fanoutTwo_eval`, `BoolCircuit.DAGCircuit.fanoutTwo_size_le`.
