<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwire_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth after hardwiring

**Claim.** Hardwiring the last $m$ inputs of $C$ produces a circuit of depth at most $	ext{depth}(C)+1$.

**Proof.** Compare depths in the original circuit with those in the hardwired circuit, allowing the latter to exceed the former by at most one. Initially, the original input depths are all zero. In the hardwired circuit the first $n$ inputs have depth zero and the newly inserted constant gates have depth one, so every corresponding initial value satisfies this comparison. The depth of a gate is one plus the maximum depth among its arguments. The depth comparison is preserved when corresponding gates are evaluated: the remapping-depth bound (`DAGGate.depth_remap_le`) shows that if each argument depth satisfies the comparison, then so does the gate depth. The general run correspondence theorem (`BoolCircuit.runWith_remap_rel`) propagates this bound through all original gates; here the remapping is the identity, so the original gate list is unchanged (`DAGGate.remap_id`). The inserted constants contribute depth-one vertices (`runWith_depth_constGates`), and the bound on their initial depths follows from `getD_le_one`. Since the output is a vertex of the circuit, applying the propagated comparison at that vertex gives the stated depth bound. The runs over the two consecutive gate lists are related by `runWith_append`.

**Key facts.** `BoolCircuit.DAGGate.depth_remap_le`, `BoolCircuit.getD_le_one`, `BoolCircuit.runWith_remap_rel`, `BoolCircuit.DAGGate.remap_id`, `BoolCircuit.runWith_append`, `BoolCircuit.runWith_depth_constGates`.
