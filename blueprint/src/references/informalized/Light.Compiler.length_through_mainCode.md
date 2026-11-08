<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.length_through_mainCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Through Main Code

**Claim.** For every program $P$, main procedure index $p_0$, and Boolean flag $d$, the concatenation of the head code and main code has length equal to the first procedure-body position determined by the frame size of $P$ and $d$.

**Proof.** The head consists of three straight-line instructions followed by one branch, so it has length four. The main statement has size $2F+11$ when the frame size is $F$ (`size_mainStmt`), and its compiled code has that same length (`length_compileStmt`). The tail code has length five when $d$ is true and two when it is false (`length_tailCode`). Thus the total length is $4+(2F+11)+igl(5	ext{ if }d,	ext{ otherwise }2igr)$. By the definitions of the main position, tail position, and first-body position, this is exactly the first-body position.

**Key facts.** `Light.Compiler.length_compileStmt`, `Light.Compiler.size_mainStmt`, `Light.Compiler.length_tailCode`.
