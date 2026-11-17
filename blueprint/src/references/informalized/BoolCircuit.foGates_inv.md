<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.foGates_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout Reduction Invariants

**Claim.** For every acyclic list of gates satisfying the stated argument conditions, the fanout reduction produces a count, gate list, and vertex map satisfying all the fanout reduction invariants.

**Proof.** Proceed by induction on the original list, building it from the end. For the empty list, the reduction starts with the empty gate list, the identity map, and count $n$, which satisfy the invariants by the empty case. For the inductive step, write the list as $old$ followed by one gate $g$. Acyclicity of the full list restricts to acyclicity of its prefix, and the gate conditions for each prefix gate follow from those for the full list. Thus the induction hypothesis gives the invariants after reducing the prefix. The appended list is acyclic by assumption, and $g$ satisfies the required argument conditions, so the one-step preservation theorem (BoolCircuit.foInv_step) applies to the prefix invariants and yields the invariants after processing $g$. Unfolding the fold defining the reduction identifies this resulting state with the reduction of the full list.

**Key facts.** `BoolCircuit.foInv_nil`, `BoolCircuit.foInv_step`.
