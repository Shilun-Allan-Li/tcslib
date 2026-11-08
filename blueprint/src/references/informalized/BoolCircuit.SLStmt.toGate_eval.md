<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.SLStmt.toGate_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Statement Gate

**Claim.** For a straight-line statement $s$ with operation $ullet$ and operands $a,b$, its associated gate evaluates to $ullet(vals[v_a],vals[v_b])$, where each list lookup outside the range returns false.

**Proof.** Unfold the gate associated with $s$ and split according to whether its two operand vertices coincide. When they coincide, the gate has one argument; for either conjunction or disjunction, applying that operation to the same Boolean value twice gives that value. When the vertices differ, the gate has both vertices as arguments. In each case, the gate's kind is conjunction when $s$ uses conjunction and disjunction when it uses disjunction, so its evaluation is exactly the stated operation on the two default-false list lookups.
