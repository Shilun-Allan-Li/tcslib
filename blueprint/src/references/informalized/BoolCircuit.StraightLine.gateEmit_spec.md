<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.StraightLine.gateEmit_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Gate Emission

**Claim.** Processing a gate with at most two arguments, whose referenced rails use only inputs and earlier lines, extends the statements validly, emits at most two statements, and returns rails that evaluate to the gate's value and its complement under the stated argument-rail hypothesis.

**Proof.** Split on the gate kind. For an AND gate, the claim is exactly the operation-emission result for conjunction; for an OR gate, it is that result for disjunction (`emitOp_spec`). For a NOT gate, the construction emits the rails for conjunction on the same arguments, then swaps the two returned rails. The conjunction emission already supplies valid statements, the size bound, and valid references for both rails. If its rails evaluate to a value and its complement, swapping them gives the complement as the NOT gate's value and the original value as the complement of that result. In this case the gate's evaluation is the negation of the conjunction of its arguments, as required.

**Key facts.** `BoolCircuit.StraightLine.emitOp_spec`.
