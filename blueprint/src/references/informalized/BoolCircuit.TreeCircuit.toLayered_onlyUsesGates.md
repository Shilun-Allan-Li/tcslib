<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.TreeCircuit.toLayered_onlyUsesGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate operations in the layered circuit

**Claim.** Every gate operation in the layered feedforward circuit associated with a Boolean circuit $c$ is the identity, the unary operation $x\mapsto 1-x_0$, or an AND operation of some finite arity.

**Proof.** Apply the corresponding gate-operation theorem for the associated DAG circuit. It says that every gate in its layered circuit belongs to the specified set of standard gate operations, which consists of the identity, the unary operation $x\mapsto 1-x_0$, and the finite-arity product operations. The tree circuit's layered construction is obtained from that DAG circuit's layered construction, so the same classification applies.

**Key facts.** `BoolCircuit.DAGCircuit.toLayered_onlyUsesGates`.
