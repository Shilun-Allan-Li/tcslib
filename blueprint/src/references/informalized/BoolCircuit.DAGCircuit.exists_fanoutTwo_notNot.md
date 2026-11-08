<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.DAGCircuit.exists_fanoutTwo_notNot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-Fanout Conversion with Strict Gates

**Claim.** A circuit whose gates have distinct arguments and the specified exact arities can be replaced by an equivalent circuit with the same gate conditions, fanout at most two, and size at most five times the original size.

**Proof.** Take the circuit produced by the strict-gate fanout-two construction. Every gate in it remains strict, so it has distinct arguments and the required arity (`BoolCircuit.DAGCircuit.fanoutTwoNN_strict`); every vertex has fanout at most two (`BoolCircuit.DAGCircuit.fanoutTwoNN_hasFanoutTwo`). The construction preserves evaluation on every input (`BoolCircuit.DAGCircuit.fanoutTwoNN_eval`). Its size is at most $n+5|C.gates|$, which is at most $5(n+|C.gates|)$, the asserted bound in terms of circuit size (`BoolCircuit.DAGCircuit.fanoutTwoNN_size_le`).

**Key facts.** `BoolCircuit.DAGCircuit.fanoutTwoNN_strict`, `BoolCircuit.DAGCircuit.fanoutTwoNN_hasFanoutTwo`, `BoolCircuit.DAGCircuit.fanoutTwoNN_eval`, `BoolCircuit.DAGCircuit.fanoutTwoNN_size_le`.
