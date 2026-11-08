<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.not_exists_straightLine_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant true separates circuit models

**Claim.** There is a well-formed acyclic Boolean circuit with fan-in at most two, no input variables, and size one that evaluates to true on every assignment, while no valid straight-line program with no input variables evaluates to true on every assignment.

**Proof.** For the circuit existence, take the constant circuit with zero inputs and value true. The constant-circuit fan-in theorem (`BoolCircuit.constCircuit_isFaninTwo`) gives its fan-in bound and well-formedness; its size is one by the definition of size when there are no inputs and no gates, and the constant-circuit evaluation theorem (`BoolCircuit.constCircuit_eval`) says that it evaluates to true for every assignment. For the nonexistence claim, suppose a straight-line program with zero inputs evaluated to true for every assignment. There is a unique assignment on the empty input type, so its evaluation would be true there. But every such program evaluates to false on zero inputs (`BoolCircuit.StraightLineProgram.eval_of_zero`), a contradiction.

**Key facts.** `BoolCircuit.constCircuit_isFaninTwo`, `BoolCircuit.constCircuit_eval`, `BoolCircuit.StraightLineProgram.eval_of_zero`.
