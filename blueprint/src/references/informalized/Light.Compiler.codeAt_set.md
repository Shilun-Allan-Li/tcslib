<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.codeAt_set -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Instruction locations in assignments

**Claim.** If the compiled assignment of $e$ to $x$ at position $pos$ is a prefix of the code beginning there, then the compiled expression is a prefix beginning at $pos$, and the address computation and store instructions form a prefix beginning at $pos+|e|$.

**Proof.** The compiled assignment is the concatenation of the compiled expression and the two instructions that compute the address of $x$ and store the expression value. The prefix decomposition theorem for code locations gives the first component as a prefix at $pos$, and the second component as a prefix at $pos$ plus the length of the first component (`WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`). The compiled-expression length is $|e|$ (`Light.Compiler.length_compileExpr`), so the second location is $pos+|e|$.

**Key facts.** `WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`, `Light.Compiler.length_compileExpr`.
