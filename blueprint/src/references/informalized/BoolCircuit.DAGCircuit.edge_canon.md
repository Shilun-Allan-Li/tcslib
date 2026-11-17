<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGCircuit.edge_canon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonicalization Preserves Edges

**Claim.** There is an edge from $i$ to $j$ in the canonical form of $C$ exactly when there is an edge from $i$ to $j$ in $C$.

**Proof.** Unfold the edge relation and the canonical circuit's gate list. In the forward direction, the gate at the specified position in the canonical list is the canonical form of some gate in the original list, because mapping a list over an option preserves the returned element in this way. Membership of $i$ among the canonical gate's arguments then implies membership among the original gate's arguments (`BoolCircuit.DAGGate.mem_canon_args`), giving the original edge. Conversely, an original edge supplies a gate at that position and an argument in its list. Use the canonical form of that gate at the same position; the same membership equivalence gives the required canonical edge.

**Key facts.** `BoolCircuit.DAGGate.mem_canon_args`.
