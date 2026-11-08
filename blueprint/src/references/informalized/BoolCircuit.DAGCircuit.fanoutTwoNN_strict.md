<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.DAGCircuit.fanoutTwoNN_strict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strictness after fanout reduction

**Claim.** Every gate in the circuit obtained from $C$ by the fanout reduction construction has distinct input vertices, with exactly one input for a NOT gate and exactly two for an AND or OR gate.

**Proof.** The invariant for the fanout reduction construction states that, when the original gate list is acyclic and each original gate is strict, every gate in the constructed list is strict (`nnGates_inv`). Apply it to the gates of $C$: acyclicity is supplied by the circuit’s topological-order condition, and strictness by the hypothesis $hC$. Its gate condition is precisely the asserted conclusion for every gate of the constructed circuit.

**Key facts.** `BoolCircuit.nnGates_inv`.
