<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Expressions.lean :: Light.Compiler.straight_compileExpr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straight instructions in expression code

**Claim.** For every expression and every natural number $k$, each instruction in the code compiling that expression starting at $k$ is straight.

**Proof.** Induct on the expression. For a constant, its code is digit code, whose instructions are straight by `Light.Compiler.straight_digitsCode`. For a variable, the two generated instructions are subtraction and load instructions, both straight by definition. For an operation, the compiled code concatenates the codes for its two subexpressions with the instruction implementing the operation. The induction hypotheses handle the subexpression codes, and the operation instruction is straight by `Light.Compiler.straight_instr`. For a load expression, the induction hypothesis handles the code for its address expression, and the final load instruction is straight by definition.

**Key facts.** `Light.Compiler.straight_digitsCode`, `Light.Compiler.straight_instr`.
