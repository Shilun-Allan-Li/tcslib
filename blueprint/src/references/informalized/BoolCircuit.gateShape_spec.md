<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.gateShape_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Representation by a Shape

**Claim.** For a gate whose operation is the identity, negation, or an AND operation of some arity, there is a wire, negated wire, or conjunction shape that evaluates identically on every assignment.

**Proof.** The existence theorem supplies a shape whose evaluation agrees with the gate on every assignment. The chosen gate shape is defined to be a witness from that theorem. Its witness property therefore gives the stated equality for the specified assignment.

**Key facts.** `BoolCircuit.exists_gateShape`.
