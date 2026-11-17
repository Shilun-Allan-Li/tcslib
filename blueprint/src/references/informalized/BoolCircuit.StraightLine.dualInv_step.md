<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.StraightLine.dualInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the Dual-Rail Invariant

**Claim.** If a gate's arguments refer only to inputs or existing vertices and the gate has at most two arguments, processing it extends the statements and rails so that the dual-rail invariant holds for the gate list with that gate appended.

**Proof.** Write the existing state as a statement list and a rail list. The gate-emission fact (`BoolCircuit.StraightLine.gateEmit_spec`) supplies the statements and new rail pair for this gate: the extended statements are valid, at most two statements are added, the new rails refer only to available lines, and those rails evaluate to the gate's value and its complement when their argument rails correctly represent the argument values. Existing rails remain at their old positions after the new pair is appended. Their references remain valid when the statement list grows, by monotonicity of the “before” condition (`BoolCircuit.SLOperand.Before.mono`), and their evaluations are unchanged by appending later statements (`BoolCircuit.SLOperand.eval_runLines_append`). The old vertices retain their values after appending a gate (`BoolCircuit.vertexValue_append`), so their rail-value equations continue to hold. At the new vertex, the appended rail pair is exactly the pair supplied by gate emission; its argument rails represent the old vertex values by the invariant, and the value of the last vertex is the new gate evaluated on those old values (`BoolCircuit.vertexValue_last`). This proves both new rail-value equations. The rail count increases by one, and the statement count increases by at most two, preserving the remaining numerical conditions.

**Key facts.** `BoolCircuit.StraightLine.gateEmit_spec`, `BoolCircuit.SLOperand.Before.mono`, `BoolCircuit.SLOperand.eval_runLines_append`, `BoolCircuit.vertexValue_append`, `BoolCircuit.vertexValue_last`.
