<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.StraightLine.dualInv_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Dual-Rail Invariant

**Claim.** With no gates or statements, assigning each input vertex the rails consisting of that input and its negation satisfies the dual-rail invariant, including the rail count, validity and reference conditions, correct values, and the bound on statement count.

**Proof.** There is one rail pair for each of the $n$ input vertices, so the rail-count condition holds. The statement list is empty and hence valid (`BoolCircuit.StraightLine.LinesValid.nil`). For each input vertex $v$, its rails are precisely the input at $v$ and its negation; both are valid references because neither depends on a statement line. The input-vertex evaluation fact (`BoolCircuit.vertexValue_input`) identifies the vertex's value with $x_v$. Consequently the two rails evaluate to $x_v$ and its complement. Finally, the number of statements is zero, which is at most twice the number of gates, also zero.

**Key facts.** `BoolCircuit.StraightLine.LinesValid.nil`, `BoolCircuit.vertexValue_input`.
