<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.codeAt_seq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Instruction locations in a sequence

**Claim.** If the compilation of the sequential composition of $s$ followed by $t$ at $pos$ is a prefix beginning at $pos$, then the compiled code for $s$ is a prefix beginning at $pos$, and the compiled code for $t$ is a prefix beginning at $pos+|s|_G$.

**Proof.** Unfolding compilation of the sequence gives the concatenation of the compiled code for $s$ at $pos$ and the compiled code for $t$ at $pos+|s|_G$. From the assumed prefix for this concatenation, its first block is a prefix at $pos$, and its second block is a prefix after the first block. The first block's length is $|s|_G$ (\texttt{length\_compileStmt}), so the second block begins at $pos+|s|_G$.

**Key facts.** `WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`, `Light.Compiler.length_compileStmt`, `WordRAM.CodeAt.cast_pos`.
