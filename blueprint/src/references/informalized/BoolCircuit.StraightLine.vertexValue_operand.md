<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.vertexValue_operand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of Available Operands

**Claim.** If the gate values at line vertices agree with the execution values of all lines, then every operand available before the end of the statement list has the same value in the gate list as in the straight-line execution.

**Proof.** Split according to the form of the operand. For an input operand, its associated vertex has value $x_k$ by the input-vertex property (BoolCircuit.vertexValue_input), which is its evaluation. For a negated input operand, the gate list consists of the input-negation gates followed by the statement gates. Since the relevant vertex lies within the first segment, appending the statement gates does not change its value (BoolCircuit.vertexValue_append); the input-negation gate computation then gives $!x_k$ (BoolCircuit.StraightLine.vertexValue_negGates). For a line operand at index $j$, availability means it is a line covered by the hypothesis that the gate value at vertex $2n+j$ equals the execution value at position $j$. That hypothesis is exactly the desired equality for this operand.

**Key facts.** `BoolCircuit.vertexValue_input`, `BoolCircuit.vertexValue_append`, `BoolCircuit.StraightLine.vertexValue_negGates`.
