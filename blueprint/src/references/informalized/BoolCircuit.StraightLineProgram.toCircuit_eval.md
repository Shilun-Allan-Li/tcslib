<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLineProgram.toCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Preserved by Circuit Translation

**Claim.** For every straight-line program and input assignment, evaluating its translated circuit gives the same Boolean value as evaluating the program.

**Proof.** The proof separates the case of an empty statement list from the case of a nonempty one. If the list is empty, its length is zero, and the output index of the translated circuit is identified with the index of its final gate. The value at that index is the evaluation of that final gate (`vertexValue_last`); unfolding the empty program and its translation shows that this is false, exactly the program's default evaluation. If the statement list is nonempty, the output index corresponds to the last statement's line. The line-value theorem says that this vertex evaluates to the value produced by running the straight-line statements (`vertexValue_slpGates_line`). Since the last line is the program's output, this is precisely the program's evaluation.

**Key facts.** `BoolCircuit.vertexValue_last`, `BoolCircuit.StraightLine.vertexValue_slpGates_line`.
