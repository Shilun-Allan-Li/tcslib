<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.DAGCircuit.fanoutTwoNN_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound after fanout reduction

**Claim.** For a strict circuit on $n$ inputs with $m$ gates, its fanout-reduced circuit has size at most $n+5m$.

**Proof.** The construction invariant bounds the number of gates in the converted list by five times the original number of gates. The converted circuit retains the same $n$ inputs, and circuit size is the number of inputs plus the number of gates. Adding $n$ to the gate-count bound gives size at most $n+5m$.

**Key facts.** `BoolCircuit.nnGates_inv`.
