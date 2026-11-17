<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Compiler.length_argsCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Argument Code

**Claim.** For any finite list of expressions and starting index, the generated argument code has length equal to the sum of the expression sizes.

**Proof.** Induct on the list of expressions, allowing the starting index to vary. The empty list generates empty code, and its size sum is zero. For a list with head $e$ and tail $es$, the code is the concatenation of the code for $e$ and the recursively generated code for $es$. The length of the first part is $\mathrm{size}(e)$ by the expression-code length theorem (Light.Compiler.length_compileExpr); the induction hypothesis gives the tail length as the sum of the tail sizes. Additivity of list length and the definition of the size sum yield the result.

**Key facts.** `Light.Compiler.length_compileExpr`.
