<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Compiler.length_compileCond -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Compiled Conditions

**Claim.** A compiled condition has length equal to its size: a less-than test contributes three instructions beyond its two expressions, and an equality test contributes four.

**Proof.** Split into the two forms of condition. For $a<b$, the compiler concatenates the compiled forms of $a$ and $b$ with three test and branch instructions. Their lengths are $\mathrm{size}(a)$ and $\mathrm{size}(b)$ by the expression-code length theorem (Light.Compiler.length_compileExpr), so the total is $\mathrm{size}(a)+\mathrm{size}(b)+3$, the defined size of this condition. For $a=b$, the same two compiled expressions are followed by four test and branch instructions, giving $\mathrm{size}(a)+\mathrm{size}(b)+4$, again its defined size.

**Key facts.** `Light.Compiler.length_compileExpr`.
