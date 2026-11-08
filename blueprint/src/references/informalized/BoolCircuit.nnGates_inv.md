<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.nnGates_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariants of the monotone gate construction

**Claim.** For every natural number $n$ and finite gate list $G$ satisfying the stated acyclicity and gate-arity assumptions, processing $G$ yields a state satisfying all the counter, acyclicity, tap, value, fanout, gate-shape, and size invariants.

**Proof.** Proceed by induction on the gate list, removing its last gate at each step. For the empty list, the initial state satisfies the invariant (`nnInv_nil`). For the inductive step, write the list as an earlier list followed by a final gate $g$. The acyclicity of the full list splits into acyclicity of the earlier list and the appropriate shifted acyclicity condition for the appended part (`gatesAcyclic_append`). The strict-gate hypothesis also restricts to the earlier list, so the induction hypothesis gives the invariant for the state after processing that prefix. The one-step preservation result then applies to this state, the acyclicity of the full list, and the strictness of $g$, yielding the invariant after processing the final gate (`nnInv_step`). This is exactly the state obtained by folding the construction over the full list.

**Key facts.** `BoolCircuit.nnInv_nil`, `BoolCircuit.gatesAcyclic_append`, `BoolCircuit.nnInv_step`.
