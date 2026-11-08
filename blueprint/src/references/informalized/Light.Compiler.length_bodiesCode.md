<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.length_bodiesCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Compiled Procedure Bodies

**Claim.** After compiling a list of procedure bodies with an epilogue appended after each statement, the final position equals the starting position plus the length of the concatenated code.

**Proof.** Induct on the list of statements. The empty list contributes no code and leaves the position unchanged. For a list beginning with $b$, first compile $b$ and append its epilogue, then handle the tail from position $pos+\mathrm{size}(b)+5$. The compiled statement has length $\mathrm{size}(b)$ (Light.Compiler.length_compileStmt), and the epilogue has length five (Light.Compiler.length_epilogue). By the induction hypothesis, the tail's code length accounts exactly for the difference between its starting and ending positions. Adding these lengths shows that the full concatenated code advances the original position to the end position.

**Key facts.** `Light.Compiler.length_compileStmt`, `Light.Compiler.length_epilogue`.
