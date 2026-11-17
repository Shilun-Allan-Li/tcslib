<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Conditions.lean :: Light.Compiler.codeAt_after_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code segment after two expressions

**Claim.** If the compiled code for $a$ at temporary index $0$, followed by that for $b$ at index $1$ and then $rest$, is a prefix beginning at $pos$, then $rest$ is a prefix beginning at $pos+\mathrm{size}(a)+\mathrm{size}(b)$.

**Proof.** First regard the given concatenation as the compiled code for $a$ followed by the remainder consisting of the compiled code for $b$ and $rest$. The prefix-suffix property of code locations (`WordRAM.CodeAt.right`) shows that this remainder begins after the first compiled expression, at $pos+\mathrm{size}(a)$; here the length of compiled expression code is its expression size (`Light.Compiler.length_compileExpr`). Apply the same property to split off the compiled code for $b$. The resulting suffix is $rest$, starting at $pos+\mathrm{size}(a)+\mathrm{size}(b)$. Associativity of addition identifies this with the claimed position.

**Key facts.** `Light.Compiler.length_compileExpr`, `WordRAM.CodeAt.right`.
