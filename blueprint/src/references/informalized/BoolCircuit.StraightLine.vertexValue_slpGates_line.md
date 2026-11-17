<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.vertexValue_slpGates_line -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Values for Valid Straight-Line Lines

**Claim.** For a valid straight-line program, each statement's gate value at vertex $2n+j$ equals the value at position $j$ in the program execution.

**Proof.** Use reverse induction on the list of statements. The empty list has no index $j$ to check. For the inductive step, write the program as $ss++[s]$. Validity restricts to the prefix $ss$, and the final statement $s$ reads only operands available before position $|ss|$. The induction hypothesis gives the claimed correspondence for all lines in $ss$.

The gate list for the extended program is the prefix gate list with $s$'s gate appended, and its execution is the prefix execution with $s$'s value appended (BoolCircuit.StraightLine.slpGates_snoc; BoolCircuit.StraightLine.runLines_snoc). For an index $j<|ss|$, the associated vertex is already present in the prefix gate list, so appending the new gate preserves its value (BoolCircuit.vertexValue_append); the corresponding execution-list entry is likewise unchanged by appending the final value. The induction hypothesis applies.

It remains to consider the last index $j=|ss|$. Its vertex is the position of the appended gate in the full gate computation, so its value is that gate's evaluation on the values produced by the prefix gates (BoolCircuit.vertexValue_last). The final execution list has length $|ss|+1$, and its entry at this last index is the appended value. The gate evaluation agrees with the statement evaluation: the gate encodes the same operation on the vertices of its two operands (BoolCircuit.SLStmt.toGate_eval). By the operand-value result, those vertices carry precisely the operands' values in the execution of $ss$. Applying the statement's Boolean operation therefore gives exactly its value in the straight-line execution.

**Key facts.** `BoolCircuit.StraightLine.slpGates_snoc`, `BoolCircuit.StraightLine.runLines_snoc`, `BoolCircuit.vertexValue_append`, `BoolCircuit.vertexValue_last`, `BoolCircuit.SLStmt.toGate_eval`, `BoolCircuit.StraightLine.vertexValue_operand`, `BoolCircuit.StraightLine.length_runLines`.
