<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Compiler.length_compileExpr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Compiled Expressions

**Claim.** For every expression and temporary-register index, the compiled expression has length equal to its size.

**Proof.** Induct on the expression, generalizing the temporary-register index. A constant compiles its binary digits, whose code length is the digit-list length by the digit-code length theorem (Light.Compiler.length_digitsCode); this is the defined size of the constant. A variable compiles to two instructions, matching its size. For a binary operation, the compiler concatenates the compiled left operand, compiled right operand, and one operation instruction. The induction hypotheses give the two operand lengths, so their sum with one is the defined size. For a load, the compiled operand is followed by one load instruction; its length is therefore the operand size plus one, as required.

**Key facts.** `Light.Compiler.length_digitsCode`.
