<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.depthAt_lt_of_arg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Decreases Along an Edge

**Claim.** If $v$ is a non-input vertex within the circuit, every vertex read by the gate at index $v-n$ has strictly smaller depth than $v$.

**Proof.** Because $v$ is not an input and is within the circuit, it has the form $n+(v-n)$ for a valid gate index. The depth-at-gate formula identifies its depth with one plus the maximum of zero and the depths of that gate's arguments (`BoolCircuit.DAGCircuit.depthAt_gate`). For any argument $a$, its depth is at most that maximum: the maximum of a finite list is at least each of its entries (`BoolCircuit.le_foldr_max`). Hence the depth of $a$ is strictly less than one plus the maximum, which is the depth of $v$.

**Key facts.** `BoolCircuit.DAGCircuit.depthAt_gate`, `BoolCircuit.le_foldr_max`.
