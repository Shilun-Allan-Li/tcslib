<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.codeAt_ite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Instruction locations in a conditional

**Claim.** If the compilation of “if $c$ then $s$ else $t$” at $q$ is a prefix of the code beginning at $q$, then the compiled condition, then-branch, jump instruction, and else-branch are prefixes at their respective stated positions.

**Proof.** Unfold the compilation of the conditional. Its four consecutive blocks are the compiled condition, the compiled then-branch, the single jump instruction, and the compiled else-branch. From the assumption that their concatenation is a prefix at $q$, each block is a prefix at the position where it occurs. The condition has length $|c|$ and the then-branch has length $|s|_G$ (\texttt{length\_compileCond} and \texttt{length\_compileStmt}); the jump occupies one instruction. Consequently the four starting positions are, in order, $q$, $q+|c|$, $q+|c|+|s|_G$, and $q+|c|+|s|_G+1$, as claimed.

**Key facts.** `WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`, `Light.Compiler.length_compileCond`, `Light.Compiler.length_compileStmt`, `WordRAM.CodeAt.cast_pos`.
