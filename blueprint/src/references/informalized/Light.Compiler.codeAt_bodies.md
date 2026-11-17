<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.codeAt_bodies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code locations for statement bodies

**Claim.** For each statement occurring at index $p$ in the list of bodies, its entry position in the entries list locates its compiled code followed by its epilogue, and that block ends no later than the end position of all bodies.

**Proof.** Proceed by induction on the list of statements. In the empty case there is no index with a statement, so the assertion is vacuous. For a nonempty list with first statement $b_0$ at position $pos$, if $p=0$, the lookup hypothesis identifies the requested statement with $b_0$. Choose $e=pos$: the first entry is $pos$, and the assumed prefix for all body code gives the required prefix for the first compiled statement and its epilogue (`WordRAM.CodeAt.left`). The end bound follows from the fact that every starting position is at most the corresponding end position (`Light.Compiler.le_endPos`). If $p$ is a successor, remove the first block from the body-code prefix using the suffix property of code locations (`WordRAM.CodeAt.right`). Its length is the first statement's size plus the epilogue size, by the compiled-statement and epilogue length identities (`Light.Compiler.length_compileStmt`, `Light.Compiler.length_epilogue`). Thus the remaining bodies begin at the next body's position. Apply the induction hypothesis there; the recursive definitions of entries and end position align its entry and bound with the original list.

**Key facts.** `Light.Compiler.le_endPos`, `Light.Compiler.length_compileStmt`, `Light.Compiler.length_epilogue`, `WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`.
