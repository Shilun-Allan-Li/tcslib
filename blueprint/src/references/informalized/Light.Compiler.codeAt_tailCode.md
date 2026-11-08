<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.codeAt_tailCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Location of the terminal code

**Claim.** For every light program $P$, procedure index $p_0$, and flag $dec$, the terminal code is a prefix of the compiled program beginning at its prescribed terminal-code position.

**Proof.** The main code is the compiled main statement followed by the terminal code. Since the whole main code occurs beginning at `mainPos`, the concatenation-prefix property gives the terminal code at the position `mainPos` plus the compiled main statement's length (`WordRAM.CodeAt.right`, `WordRAM.CodeAt.cast_pos`). That length is the size of the main statement (`Light.Compiler.length_compileStmt`), and the main statement's size formula is $2F+11$ (`Light.Compiler.size_mainStmt`). Unfolding `tailPos` identifies this position with `tailPos (frameSize P)`.

**Key facts.** `WordRAM.CodeAt.right`, `Light.Compiler.length_compileStmt`, `Light.Compiler.size_mainStmt`, `WordRAM.CodeAt.cast_pos`.
