<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.DAGCircuit.toStraightLine_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the straight-line program

**Claim.** For every Boolean input assignment, the straight-line program constructed from a DAG circuit with at most two arguments per gate has the same output as the circuit.

**Proof.** The dual-rail invariant says that after processing all gates, the first rail for each vertex evaluates to that vertex's circuit value, and the constructed straight-line lines evaluate as specified by their sequential execution. In particular, the first rail for the output vertex evaluates to the circuit output. The constructed program appends one final AND statement whose two operands are both that rail. Its value is therefore the rail's value, since $b\land b=b$. The straight-line program's length is the number of preceding lines plus this last statement, so its evaluation selects precisely this appended result. Hence the program and the circuit have equal outputs.

**Key facts.** `BoolCircuit.StraightLine.dualRail_inv`, `BoolCircuit.StraightLine.runLines_snoc`, `BoolCircuit.StraightLine.length_runLines`.
